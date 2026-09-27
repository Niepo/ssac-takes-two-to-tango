import ast
import hashlib
import re
import unicodedata
import warnings
from collections import defaultdict
from itertools import combinations
from pathlib import Path


import numpy as np
import pandas as pd
import xgboost as xgb
import socceraction.spadl.config as spadlcfg
import socceraction.vaep.features as fs
import socceraction.vaep.formula as vaep
import socceraction.vaep.labels as lab
from sklearn.metrics import brier_score_loss, log_loss, roc_auc_score


warnings.simplefilter(action="ignore", category=pd.errors.PerformanceWarning)


# =============================================================================
# PATHS
# =============================================================================
DOCS_DIR  = Path.home() / "Documents"
LIGAS_DIR = DOCS_DIR / "Ligas Eventing"   # <League>/<season>/preprocessed_<CODE>_<season>.csv
DATA_DIR  = DOCS_DIR / "VAEP nuevo"       # actions_vaep_<CODE>.csv, joi_pairs_<CODE>.csv
DATA_DIR.mkdir(parents=True, exist_ok=True)




# =============================================================================
# 1) OPTA EVENTS -> SPADL ACTIONS
# =============================================================================
def parse_quals(qs):
   if pd.isna(qs):
       return []
   try:
       return ast.literal_eval(qs)
   except Exception:
       return []




def has_q(quals, qid):
   for q in quals:
       t = q.get("type", {})
       if isinstance(t, dict) and t.get("value") == qid:
           return True
   return False




def parse_bool(v):
   if pd.isna(v):
       return False
   if isinstance(v, bool):
       return v
   return str(v).strip().lower() in {"true", "1", "yes", "y", "t"}




def shot_bodypart(quals):
   if has_q(quals, 15):
       return "head"
   if has_q(quals, 72) or has_q(quals, 20):
       return "foot"
   if has_q(quals, 21):
       return "other"
   return "foot"




def to_spadl_xy(x, y, flip_y=True):
   x_m = (x / 100.0) * 105.0
   y_m = (1.0 - y / 100.0) * 68.0 if flip_y else (y / 100.0) * 68.0
   return round(x_m, 2), round(y_m, 2)




def map_row(row):
   """Return (type_name, result_name, bodypart_name), or None if no SPADL equivalent."""
   quals = row["_quals"]
   eid   = int(row["event_id"])


   type_name     = None
   result_name   = None
   bodypart_name = "foot"


   outcome       = str(row.get("outcome_type", "")).strip().lower()
   outcome_value = row.get("outcome_value", None)


   if outcome in {"successful", "success", "won"}:
       successful = True
   elif outcome in {"unsuccessful", "fail", "failed", "lost"}:
       successful = False
   elif outcome_value in {1, 1.0, True}:
       successful = True
   else:
       successful = False


   if eid in (1, 2):
       if has_q(quals, 107):
           type_name = "throw_in"
       elif has_q(quals, 124):
           type_name = "goalkick"
       elif has_q(quals, 6):
           type_name = "corner_crossed" if has_q(quals, 2) else "corner_short"
       elif has_q(quals, 5):
           type_name = "freekick_crossed" if has_q(quals, 2) else "freekick_short"
       else:
           type_name = "cross" if has_q(quals, 2) else "pass"
       result_name   = "offside" if eid == 2 else ("success" if successful else "fail")
       bodypart_name = "head" if has_q(quals, 15) else "foot"


   elif eid == 3:
       type_name   = "take_on"
       result_name = "success" if successful and not has_q(quals, 211) else "fail"


   elif eid == 4:
       if row.get("outcome_value", None) == 1:
           return None
       type_name = "foul"
       ct = str(row.get("cardType", "")).lower()
       if "red" in ct:
           result_name = "red_card"
       elif "yellow" in ct:
           result_name = "yellow_card"
       else:
           result_name = "fail"


   elif eid == 7:
       type_name   = "tackle"
       result_name = "success" if row.get("outcome_value", 0) == 1 else "fail"
   elif eid == 8:
       type_name   = "interception"
       result_name = "success"
   elif eid == 12:
       type_name     = "clearance"
       result_name   = "success"
       bodypart_name = "head" if has_q(quals, 15) else "foot"


   elif eid in (13, 14, 15, 16):
       is_own = parse_bool(row.get("isOwnGoal")) or has_q(quals, 28)
       if has_q(quals, 9):
           type_name = "penalty_shot"
       elif has_q(quals, 26) or has_q(quals, 97):
           type_name = "freekick_shot"
       else:
           type_name = "shot"
       if eid == 16 and is_own:
           result_name = "owngoal"
       elif eid == 16:
           result_name = "goal"
       else:
           result_name = "fail"
       bodypart_name = shot_bodypart(quals)


   elif eid == 10:
       if has_q(quals, 94):
           return None
       type_name, result_name, bodypart_name = "keeper_save", "success", "other"
   elif eid == 11:
       type_name, result_name, bodypart_name = "keeper_claim", "success", "other"
   elif eid == 41:
       type_name, result_name, bodypart_name = "keeper_punch", "success", "other"
   elif eid in (52, 54):
       type_name, result_name, bodypart_name = "keeper_pick_up", "success", "other"


   elif eid == 61:
       if row.get("outcome_value", None) == 1:
           return None
       type_name   = "bad_touch"
       result_name = "fail"


   elif eid == 49:
       type_name   = "interception"
       result_name = "success"


   elif eid in (18, 20):
       type_name, result_name, bodypart_name = "substitution_out", "success", None
   elif eid in (19, 21):
       type_name, result_name, bodypart_name = "substitution_in", "success", None


   else:
       return None


   return type_name, result_name, bodypart_name




def add_synthetic_dribbles(actions, max_dt=10.0, min_dist=5.0, max_dist=60.0):
   """Insert a carry between consecutive same-team actions separated in space."""
   a = actions.sort_values(["game_id", "period_id", "time_seconds_abs", "action_id"]).copy()
   g = a.groupby("game_id", group_keys=False)


   a["next_team_id"]     = g["team_id"].shift(-1)
   a["next_period_id"]   = g["period_id"].shift(-1)
   a["next_time_abs"]    = g["time_seconds_abs"].shift(-1)
   a["next_start_x"]     = g["start_x"].shift(-1)
   a["next_start_y"]     = g["start_y"].shift(-1)
   a["next_player_name"] = g["player_name"].shift(-1)
   a["next_team_name"]   = g["team_name"].shift(-1)
   a["next_rival_name"]  = g["rival_name"].shift(-1)


   a["dt"]   = a["next_time_abs"] - a["time_seconds_abs"]
   dx        = a["next_start_x"] - a["end_x"]
   dy        = a["next_start_y"] - a["end_y"]
   a["dist"] = np.sqrt(dx * dx + dy * dy)


   cond = (
       (a["team_id"] == a["next_team_id"]) &
       (a["period_id"] == a["next_period_id"]) &
       a["dt"].notna() &
       (a["dt"] > 0) & (a["dt"] <= max_dt) &
       (a["dist"] >= min_dist) & (a["dist"] <= max_dist)
   )
   c = a.loc[cond]


   dribbles = pd.DataFrame({
       "league":               c["league"].values,
       "season":               c["season"].values,
       "game_id":              c["game_id"].values,
       "period_id":            c["period_id"].values,
       "time_seconds_abs":     (c["time_seconds_abs"] + c["next_time_abs"]) / 2.0,
       "team_id":              c["team_id"].values,
       "player_id":            c["player_id"].values,
       "player_name":          c["next_player_name"].values,
       "receiver_player_name": None,
       "team_name":            c["next_team_name"].values,
       "rival_name":           c["next_rival_name"].values,
       "start_x":              c["end_x"].values,
       "start_y":              c["end_y"].values,
       "end_x":                c["next_start_x"].values,
       "end_y":                c["next_start_y"].values,
       "type_name":            "dribble",
       "result_name":          "success",
       "bodypart_name":        "foot",
   })


   out = pd.concat([a[actions.columns], dribbles], ignore_index=True)
   out = out.sort_values(["game_id", "period_id", "time_seconds_abs"], kind="mergesort")
   out["action_id"] = out.groupby("game_id").cumcount()
   return out.reset_index(drop=True)




league_files = {}
for league_dir in sorted(LIGAS_DIR.iterdir()):
   if league_dir.is_dir():
       files = sorted(league_dir.glob("**/preprocessed_*.csv"))
       if files:
           league_files[league_dir.name] = files


spadl_frames = []
for league_name, files in league_files.items():
   print(f"Converting to SPADL: {league_name} ({len(files)} season(s))")


   dfs = []
   for f in files:
       df_i = pd.read_csv(f, low_memory=False)
       df_i["season"] = f.parent.name
       df_i["league"] = league_name
       dfs.append(df_i)
   df = pd.concat(dfs, ignore_index=True)


   df["_quals"] = df["qualifiers"].apply(parse_quals)
   mapped = df.apply(map_row, axis=1)
   keep   = mapped.notna()
   df2    = df.loc[keep].copy()
   df2[["type_name", "result_name", "bodypart_name"]] = list(mapped[keep])


   df2[["start_x", "start_y"]] = df2.apply(
       lambda r: pd.Series(to_spadl_xy(r["x"], r["y"])), axis=1)
   df2[["end_x", "end_y"]] = df2.apply(
       lambda r: pd.Series(to_spadl_xy(r["endX"], r["endY"])), axis=1)


   df2["game_id"]          = df2["matchId"]
   df2["period_id"]        = df2["period_id"].astype(int)
   df2["time_seconds_abs"] = df2["time_seconds"].astype(float)
   df2["time_seconds"]     = (
       df2["time_seconds_abs"]
       - df2.groupby(["game_id", "period_id"])["time_seconds_abs"].transform("min")
   )
   df2 = df2.sort_values(["game_id", "period_id", "time_seconds", "eventId", "teamId"],
                         kind="mergesort")
   df2["action_id"] = df2.groupby("game_id").cumcount()


   actions = df2[[
       "league", "season", "game_id", "action_id", "period_id", "time_seconds_abs",
       "teamId", "playerId", "jugador", "receiver_playerName", "TeamName", "TeamRival",
       "start_x", "start_y", "end_x", "end_y",
       "type_name", "result_name", "bodypart_name",
   ]].rename(columns={
       "teamId":              "team_id",
       "playerId":            "player_id",
       "jugador":             "player_name",
       "TeamName":            "team_name",
       "TeamRival":           "rival_name",
       "receiver_playerName": "receiver_player_name",
   })


   actions = add_synthetic_dribbles(actions)
   actions["league_code"] = files[0].stem.split("_")[1]
   spadl_frames.append(actions)
   print(f"  {len(df):,} raw events -> {len(actions):,} SPADL actions")




# =============================================================================
# 2) VAEP: TRAIN ON 21-22, VALUE ACTIONS IN 22-23 TO 25-26
# =============================================================================
actions = pd.concat(spadl_frames, ignore_index=True)


actions["game_id_orig"] = actions["game_id"].astype(str)
actions["team_id_orig"] = actions["team_id"].astype(str)
actions["game_id"], _   = pd.factorize(actions["game_id_orig"], sort=True)
actions["team_id"], _   = pd.factorize(actions["team_id_orig"], sort=True)


actions = actions.rename(columns={"time_seconds_abs": "time_seconds_overall"})
actions["time_seconds"] = actions["time_seconds_overall"]
actions.loc[actions["period_id"] == 2, "time_seconds"] = (
   actions.loc[actions["period_id"] == 2, "time_seconds_overall"] - 2700
)


for col in ["game_id", "action_id", "period_id", "team_id"]:
   actions[col] = actions[col].astype(int)
actions = actions.sort_values(
   ["game_id", "period_id", "time_seconds_overall", "action_id"], kind="mergesort"
).reset_index(drop=True)


actions["type_name"] = actions["type_name"].replace({
   "penalty_shot":  "shot_penalty",
   "freekick_shot": "shot_freekick",
})


SHOT_TYPES = {"shot", "shot_penalty", "shot_freekick"}
actions.loc[
   actions["type_name"].isin(SHOT_TYPES) & (actions["result_name"] == "goal"), "result_name"
] = "success"


actions["type_id"]     = actions["type_name"].map({n: i for i, n in enumerate(spadlcfg.actiontypes)})
actions["result_id"]   = actions["result_name"].map({n: i for i, n in enumerate(spadlcfg.results)})
actions["bodypart_id"] = actions["bodypart_name"].map({n: i for i, n in enumerate(spadlcfg.bodyparts)})


SUB_TYPES = {"substitution_out", "substitution_in"}


actions_full = actions.copy()
actions_full["row_key"] = (
   actions_full["league_code"].astype(str) + "-" +
   actions_full["game_id"].astype(str) + "-" +
   actions_full["action_id"].astype(str)
)
actions_vaep = actions_full[~actions_full["type_name"].isin(SUB_TYPES)].copy()


NB_PREV_ACTIONS = 3
xfns = [
   fs.actiontype_onehot,
   fs.bodypart_onehot,
   fs.result_onehot,
   fs.startlocation,
   fs.endlocation,
   fs.movement,
   fs.space_delta,
   fs.startpolar,
   fs.endpolar,
   fs.time_delta,
   fs.team,
   fs.goalscore,
]




def compute_features_for_game(game_actions):
   game_actions = game_actions.sort_values(["period_id", "time_seconds", "action_id"]).reset_index(drop=True)
   gamestates = fs.gamestates(game_actions, NB_PREV_ACTIONS)
   return pd.concat([fn(gamestates) for fn in xfns], axis=1)




def compute_labels_for_game(game_actions):
   Y = pd.concat([lab.scores(game_actions), lab.concedes(game_actions)], axis=1)
   Y.columns = ["scores", "concedes"]
   return Y




def build_xy_for_games(actions_df, game_ids):
   X_parts, Y_parts, idx_parts = [], [], []
   for gid in game_ids:
       g = actions_df[actions_df["game_id"] == gid].copy()
       if g.empty:
           continue
       g = g.sort_values(["period_id", "time_seconds", "action_id"]).reset_index(drop=True)
       X_parts.append(compute_features_for_game(g))
       Y_parts.append(compute_labels_for_game(g))
       idx_parts.append(g[["game_id", "action_id"]].copy())
   X   = pd.concat(X_parts, axis=0).reset_index(drop=True)
   Y   = pd.concat(Y_parts, axis=0).reset_index(drop=True)
   idx = pd.concat(idx_parts, axis=0).reset_index(drop=True)
   return X, Y, idx




TRAIN_SEASON = "21-22"
TEST_SEASONS = ["22-23", "23-24", "24-25", "25-26"]


train_game_ids = actions_vaep.loc[actions_vaep["season"] == TRAIN_SEASON, "game_id"].dropna().unique().tolist()
test_game_ids  = actions_vaep.loc[actions_vaep["season"].isin(TEST_SEASONS), "game_id"].dropna().unique().tolist()
print(f"Train games: {len(train_game_ids):,} | Test games: {len(test_game_ids):,}")


X_train, Y_train, idx_train = build_xy_for_games(actions_vaep, train_game_ids)
X_test,  Y_test,  idx_test  = build_xy_for_games(actions_vaep, test_game_ids)
X_test = X_test.reindex(columns=X_train.columns, fill_value=0)




def fit_xgb_classifier(X, y):
   model = xgb.XGBClassifier(
       n_estimators     = 1000,
       learning_rate    = 0.05,
       max_depth        = 3,
       min_child_weight = 5,
       subsample        = 0.8,
       colsample_bytree = 0.8,
       reg_lambda       = 1.0,
       n_jobs           = -1,
       tree_method      = "hist",
       eval_metric      = "logloss",
       random_state     = 42,
   )
   model.fit(X, y.astype(int))
   return model




scores_model   = fit_xgb_classifier(X_train, Y_train["scores"])
concedes_model = fit_xgb_classifier(X_train, Y_train["concedes"])


p_scores   = scores_model.predict_proba(X_test)[:, 1]
p_concedes = concedes_model.predict_proba(X_test)[:, 1]


pred_test = idx_test.copy()
pred_test["p_scores"]   = p_scores
pred_test["p_concedes"] = p_concedes




def report(y_true, p_pred, name):
   y_true = np.asarray(y_true, dtype=int)
   p_pred = np.asarray(p_pred, dtype=float)
   m      = ~np.isnan(p_pred)
   y_true, p_pred = y_true[m], p_pred[m]
   base   = np.full_like(y_true, float(y_true.mean()), dtype=float)
   print(name)
   print(f"  event rate : {y_true.mean():.4f}")
   print(f"  log-loss   : {log_loss(y_true, p_pred):.4f}  "
         f"(ratio vs base: {log_loss(y_true, p_pred) / log_loss(y_true, base):.3f})")
   print(f"  brier      : {brier_score_loss(y_true, p_pred):.4f}  "
         f"(ratio vs base: {brier_score_loss(y_true, p_pred) / brier_score_loss(y_true, base):.3f})")
   print(f"  AUC-ROC    : {roc_auc_score(y_true, p_pred):.4f}")




report(Y_test["scores"],   p_scores,   "Scores model")
report(Y_test["concedes"], p_concedes, "Concedes model")


actions_test = actions_vaep[actions_vaep["game_id"].isin(test_game_ids)].copy()
actions_test = actions_test.merge(pred_test, on=["game_id", "action_id"], how="left")
actions_test = actions_test.sort_values(["game_id", "period_id", "time_seconds"]).reset_index(drop=True)


vals = vaep.value(actions_test, actions_test["p_scores"], actions_test["p_concedes"])


actions_out = pd.concat(
   [actions_test[["game_id", "action_id", "league_code", "p_scores", "p_concedes"]], vals],
   axis=1,
)
actions_out["row_key"] = (
   actions_out["league_code"].astype(str) + "-" +
   actions_out["game_id"].astype(str) + "-" +
   actions_out["action_id"].astype(str)
)


actions_final = actions_full.merge(
   actions_out[["row_key", "p_scores", "p_concedes",
                "offensive_value", "defensive_value", "vaep_value"]],
   on="row_key",
   how="left",
)


for league_code in sorted(actions_final["league_code"].dropna().unique()):
   subset = actions_final[actions_final["league_code"] == league_code]
   subset.to_csv(DATA_DIR / f"actions_vaep_{league_code}.csv", index=False)
   print(f"  {league_code}: {len(subset):,} actions -> actions_vaep_{league_code}.csv")




# =============================================================================
# 3) JOINT OFFENSIVE IMPACT (JOI) PER PAIR-SEASON
# =============================================================================
CROSS_TYPES     = {"cross", "corner_crossed", "freekick_crossed"}
SUCCESS_RESULTS = {"success"}
DRIBBLE_TYPES   = {"dribble"}
TERMINAL_TYPES  = {"shot", "pass", "cross", "take_on"}


df = actions_final.copy()
for col in ["player_name", "receiver_player_name", "result_name", "type_name"]:
   df[col] = df[col].replace({"": np.nan})
df = df.sort_values(["league_code", "season", "game_id", "action_id"]).reset_index(drop=True)




def canon_name(x):
   if pd.isna(x):
       return np.nan
   x = str(x).strip().lower()
   x = unicodedata.normalize("NFKD", x)
   x = "".join(ch for ch in x if not unicodedata.combining(ch))
   x = re.sub(r"[^a-z0-9\s]", " ", x)
   x = re.sub(r"\s+", " ", x).strip()
   return x if x else np.nan




df["player_name_c"]   = df["player_name"].map(canon_name)
df["receiver_name_c"] = df["receiver_player_name"].map(canon_name)
df["team_name_c"]     = df["team_name"].astype(str).str.strip().str.lower()
df["season_c"]        = df["season"].astype(str).str.strip().str.lower()


# Fill missing cross receivers from the next same-team action
df["next_game_id"]     = df["game_id"].shift(-1)
df["next_team_id"]     = df["team_id"].shift(-1)
df["next_player_name"] = df["player_name"].shift(-1)
to_fill = (
   df["next_game_id"].eq(df["game_id"]) &
   df["next_team_id"].eq(df["team_id"]) &
   df["type_name"].isin(CROSS_TYPES) &
   df["result_name"].str.lower().isin(SUCCESS_RESULTS) &
   df["next_player_name"].notna() &
   df["receiver_player_name"].isna()
)
df.loc[to_fill, "receiver_player_name"] = df.loc[to_fill, "next_player_name"]
df = df.drop(columns=["next_game_id", "next_team_id", "next_player_name"])




def make_uid(parts):
   s = "||".join("" if pd.isna(p) else str(p) for p in parts)
   return hashlib.md5(s.encode("utf-8")).hexdigest()




df["player_uid_game"] = df.apply(
   lambda r: make_uid([r["league_code"], r["game_id"], r["team_name_c"], r["player_name_c"]]), axis=1)
df["receiver_uid_game"] = df.apply(
   lambda r: make_uid([r["league_code"], r["game_id"], r["team_name_c"], r["receiver_name_c"]]), axis=1)
df["player_uid_season"] = df.apply(
   lambda r: make_uid([r["league_code"], r["season_c"], r["team_name_c"], r["player_name_c"]]), axis=1)
df["receiver_uid_season"] = df.apply(
   lambda r: make_uid([r["league_code"], r["season_c"], r["team_name_c"], r["receiver_name_c"]]), axis=1)


# Interactions: A -> B (2-step) or A -> B dribbles -> B terminal action (3-step)
df = df.sort_values(["league_code", "season", "game_id", "period_id", "action_id"]).reset_index(drop=True)
for n in (1, 2):
   for col, alias in [("game_id", "g"), ("team_name_c", "t"), ("player_uid_game", "p"),
                      ("type_name", "ty"), ("vaep_value", "v")]:
       df[f"{alias}{n}"] = df[col].shift(-n)


same_1 = df["g1"].eq(df["game_id"]) & df["t1"].eq(df["team_name_c"])
same_2 = df["g2"].eq(df["game_id"]) & df["t2"].eq(df["team_name_c"])


is_2 = (
   same_1 &
   df["player_uid_game"].notna() & df["receiver_uid_game"].notna() & df["p1"].notna() &
   df["receiver_uid_game"].eq(df["p1"])
)
is_3 = (
   same_1 & same_2 &
   df["player_uid_game"].notna() & df["receiver_uid_game"].notna() &
   df["p1"].notna() & df["p2"].notna() &
   df["receiver_uid_game"].eq(df["p1"]) &
   df["p2"].eq(df["p1"]) &
   df["ty1"].isin(DRIBBLE_TYPES) &
   df["ty2"].isin(TERMINAL_TYPES)
)


BASE_COLS = ["season", "game_id", "team_name_c",
            "player_uid_game", "receiver_uid_game",
            "player_uid_season", "receiver_uid_season", "vaep_value"]


inter2 = df.loc[is_2 & ~is_3, BASE_COLS + ["v1"]].copy()
inter2["interaction_vaep"] = inter2["vaep_value"].fillna(0) + inter2["v1"].fillna(0)


inter3 = df.loc[is_3, BASE_COLS + ["v1", "v2"]].copy()
inter3["interaction_vaep"] = (inter3["vaep_value"].fillna(0)
                             + inter3["v1"].fillna(0)
                             + inter3["v2"].fillna(0))


interactions = pd.concat([inter2, inter3], ignore_index=True)
interactions["p1"] = interactions[["player_uid_season", "receiver_uid_season"]].min(axis=1)
interactions["p2"] = interactions[["player_uid_season", "receiver_uid_season"]].max(axis=1)


pair_joi = (
   interactions.groupby(["p1", "p2"], as_index=False)["interaction_vaep"]
   .sum()
   .rename(columns={"interaction_vaep": "total_joi"})
)


# Minutes on pitch per player-game (substitution-aware)
first_last = (
   df.loc[df["player_uid_game"].notna(), ["game_id", "player_uid_game", "time_seconds_overall"]]
   .groupby(["game_id", "player_uid_game"])["time_seconds_overall"]
   .agg(first_action_s="min", last_action_s="max")
   .reset_index()
)
match_dur = (
   df.groupby("game_id")["time_seconds_overall"].max()
   .rename("match_duration_s").reset_index()
)
subs = df.loc[
   df["type_name"].isin(["substitution_in", "substitution_out"]),
   ["game_id", "player_uid_game", "type_name", "time_seconds_overall"],
]
sub_in = (
   subs[subs["type_name"].eq("substitution_in")]
   .groupby(["game_id", "player_uid_game"])["time_seconds_overall"]
   .min().rename("sub_in_s").reset_index()
)
sub_out = (
   subs[subs["type_name"].eq("substitution_out")]
   .groupby(["game_id", "player_uid_game"])["time_seconds_overall"]
   .min().rename("sub_out_s").reset_index()
)


players = (
   first_last
   .merge(match_dur, on="game_id", how="left")
   .merge(sub_in,   on=["game_id", "player_uid_game"], how="left")
   .merge(sub_out,  on=["game_id", "player_uid_game"], how="left")
)
players["start_s"] = players["sub_in_s"].fillna(0)
players["end_candidate_s"] = players["sub_out_s"].fillna(players["match_duration_s"])
bad_sub_out = players["sub_out_s"].notna() & (players["last_action_s"] > players["sub_out_s"] + 1.0)
players["end_s"] = np.where(bad_sub_out, players["match_duration_s"], players["end_candidate_s"])


# Minutes together per pair-game
pair_minutes = defaultdict(float)
players2 = players.dropna(subset=["player_uid_game"]).drop_duplicates(["game_id", "player_uid_game"])
for gid, g in players2.groupby("game_id"):
   p = g["player_uid_game"].astype(str).str.strip().to_numpy()
   s = g["start_s"].to_numpy()
   e = g["end_s"].to_numpy()
   for i, j in combinations(range(len(p)), 2):
       overlap_s = max(0.0, min(e[i], e[j]) - max(s[i], s[j]))
       if overlap_s > 0:
           a, b = (p[i], p[j]) if p[i] <= p[j] else (p[j], p[i])
           pair_minutes[(a, b)] += overlap_s / 60.0


pair_minutes_df = pd.DataFrame(
   [(a, b, m) for (a, b), m in pair_minutes.items()],
   columns=["p1_game", "p2_game", "minutes_together"],
)


uid_to_season = (
   df[["player_uid_game", "player_uid_season"]]
   .dropna().drop_duplicates()
   .set_index("player_uid_game")["player_uid_season"]
)
pair_minutes_df["p1_season"] = pair_minutes_df["p1_game"].map(uid_to_season)
pair_minutes_df["p2_season"] = pair_minutes_df["p2_game"].map(uid_to_season)
pair_minutes_df["p1"] = pair_minutes_df[["p1_season", "p2_season"]].min(axis=1)
pair_minutes_df["p2"] = pair_minutes_df[["p1_season", "p2_season"]].max(axis=1)


pair_agg = (
   pair_minutes_df.groupby(["p1", "p2"], as_index=False)
   .agg(minutes_together=("minutes_together", "sum"))
   .merge(pair_joi, on=["p1", "p2"], how="left")
)
pair_agg["total_joi"] = pair_agg["total_joi"].fillna(0)
pair_agg = pair_agg.loc[pair_agg["minutes_together"] > 0].copy()
pair_agg["joi_per90"] = pair_agg["total_joi"] / (pair_agg["minutes_together"] / 90.0)
pair_agg = pair_agg.sort_values("joi_per90", ascending=False).reset_index(drop=True)


id_to_name = (
   df.loc[df["player_uid_season"].notna(), ["player_uid_season", "player_name"]]
   .dropna().drop_duplicates()
   .groupby("player_uid_season")["player_name"]
   .agg(lambda s: s.value_counts().index[0])
   .to_dict()
)
uid_meta = (
   df[["player_uid_season", "season", "league_code"]]
   .dropna(subset=["player_uid_season"])
   .drop_duplicates("player_uid_season")
   .set_index("player_uid_season")
)


pair_agg["player1_name"] = pair_agg["p1"].map(id_to_name)
pair_agg["player2_name"] = pair_agg["p2"].map(id_to_name)
pair_agg["season"]       = pair_agg["p1"].map(uid_meta["season"])
pair_agg["league_code"]  = pair_agg["p1"].map(uid_meta["league_code"])
pair_agg = pair_agg[["league_code", "season", "player1_name", "player2_name",
                    "total_joi", "minutes_together", "joi_per90"]]


for lc in sorted(pair_agg["league_code"].dropna().unique()):
   subset = pair_agg[pair_agg["league_code"] == lc]
   subset.to_csv(DATA_DIR / f"joi_pairs_{lc}.csv", index=False)
   print(f"  {lc}: {len(subset):,} pairs -> joi_pairs_{lc}.csv")
