library(data.table)
library(bit64)
library(stringi)
library(ggplot2)
library(scales)
library(writexl)
library(readxl)
library(httr)
library(rvest)
library(xml2)
library(transport)

# ============================================================
# 0) PATHS
# ============================================================
docs_dir <- path.expand("~/Documents")

# actions_vaep_*.csv, joi_pairs_*.csv and scores_of_def_*.csv
vaep_dir <- file.path(docs_dir, "VAEP nuevo")

# Preprocessed event-stream CSVs (minutes + positions)
pre_base_dirs <- file.path(docs_dir, "Ligas Eventing", c(
  "England Premier League",
  "France Ligue 1",
  "Germany Bundesliga",
  "Italy Serie A",
  "Spain La Liga",
  "Spanish Segunda Division"
))

team_map_path       <- file.path(docs_dir, "New downloads", "team_id_name_map.csv")
mv_manual_fill_path <- file.path(docs_dir, "missing_mv_data.xlsx")
decomp_path         <- file.path(docs_dir, "pair_prediction_detail.csv")

# ============================================================
# 1) CONSTANTS
# ============================================================
PITCH_LEN <- 105
PITCH_WID <- 68

# Zone grid
nx <- 12L
ny <- 8L
K  <- nx * ny
zone_cols <- as.character(seq_len(K))

zone_centres_xy <- data.frame(
  x = ((seq_len(K) - 1L) %%  nx + 0.5) * (PITCH_LEN / nx),
  y = ((seq_len(K) - 1L) %/% nx + 0.5) * (PITCH_WID / ny)
)

SIGMA_M      <- 8      # Gaussian smoothing bandwidth (metres)
MIN_MINUTES  <- 450    # Minimum minutes together for a pair-season
MODEL_MIN_MINUTES <- 1500
PASS_TYPES   <- c("pass", "cross")
ROLE_ALPHA   <- 10     # Laplace smoothing for role profiles
SEED         <- 130L

# ============================================================
# 2) HELPER FUNCTIONS
# ============================================================

# Normalise season strings to "YY-YY" format (e.g. "2022-23" -> "22-23")
norm_season <- function(s) {
  s <- as.character(s)
  s <- stringi::stri_trim_both(s)
  s <- stringi::stri_replace_all_regex(s, "[/_]", "-")
  s <- stringi::stri_replace_all_regex(s, "\\s+", "")
  m <- stringi::stri_match_first_regex(s, "^(?:20)?(\\d{2})-(?:20)?(\\d{2})$")
  ifelse(!is.na(m[,1]), paste0(m[,2], "-", m[,3]), NA_character_)
}

# Return the season preceding the given "YY-YY" season
prev_season <- function(season_yy) {
  season_yy <- as.character(season_yy)
  ok  <- !is.na(season_yy) & grepl("^\\d{2}-\\d{2}$", season_yy)
  out <- rep(NA_character_, length(season_yy))
  if (any(ok)) {
    s1       <- as.integer(substr(season_yy[ok], 1, 2))
    out[ok]  <- sprintf("%02d-%02d", s1 - 1L, s1)
  }
  out
}

# Lowercase, trim, strip accents; return NA for blank/null strings
std_name <- function(x, strip_accents = TRUE) {
  x <- as.character(x)
  x <- stringi::stri_trim_both(x)
  x <- stringi::stri_replace_all_regex(x, "\\s+", " ")
  x <- tolower(x)
  if (strip_accents) x <- stringi::stri_trans_general(x, "Latin-ASCII")
  x[x %in% c("", "na", "nan", "null")] <- NA_character_
  x
}

# Stop with an informative message if required columns are absent
assert_has_cols <- function(dt, cols, dt_name = "data") {
  miss <- setdiff(cols, names(dt))
  if (length(miss) > 0)
    stop(dt_name, " is missing columns: ", paste(miss, collapse = ", "))
  invisible(TRUE)
}

# Validate that coordinates are in 105x68 metre space; stop with hints otherwise
check_coords_105x68_or_stop <- function(dt, pitch_len = 105, pitch_wid = 68, tol = 0.5) {
  for (cc in c("start_x","start_y","end_x","end_y"))
    dt[, (cc) := suppressWarnings(as.numeric(get(cc)))]

  rng <- dt[, .(
    x_min = min(pmin(start_x, end_x), na.rm = TRUE),
    x_max = max(pmax(start_x, end_x), na.rm = TRUE),
    y_min = min(pmin(start_y, end_y), na.rm = TRUE),
    y_max = max(pmax(start_y, end_y), na.rm = TRUE)
  ), by = season][order(season)]

  cat("\n--- Coordinate diagnostic by season (raw, no scaling applied) ---\n")
  print(rng)

  bad <- FALSE
  for (i in seq_len(nrow(rng))) {
    s   <- rng$season[i]
    xmn <- rngxmin[i];xmx<-rngx_max[i]
    ymn <- rngymin[i];ymx<-rngy_max[i]

    if (xmn >= -tol && ymn >= -tol && xmx <= pitch_len + tol && ymx <= pitch_wid + tol) next
    if (xmn >= -tol && ymn >= -tol && xmx <= pitch_wid + tol && ymx <= pitch_len + tol)
      stop("Season ", s, ": coordinates look SWAPPED (x<=68, y<=105). Transform upstream and rerun.")
    if (xmn >= -tol && ymn >= -tol && xmx <= 100.5 && ymx <= 100.5)
      stop("Season ", s, ": coordinates look like 0..100. Transform upstream to metres and rerun.")
    if (xmn >= -tol && ymn >= -tol && xmx <= 120.5 && ymx <= 80.5)
      stop("Season ", s, ": coordinates look like ~120x80. Transform upstream to metres and rerun.")
    if (xmn >= -tol && ymn >= -tol && xmx <= 1.5 && ymx <= 1.5)
      stop("Season ", s, ": coordinates look like 0..1 normalised. Transform upstream to metres and rerun.")
    bad <- TRUE
  }
  if (bad) stop("Some seasons are not in expected 105x68 metres. Please transform upstream.")
  cat("OK: coordinates look like metres on 105x68 (x<=105, y<=68) for all seasons.\n")
  invisible(TRUE)
}

# Map (x, y) coordinates to a zone ID in the nx*ny grid
zone_id <- function(x, y, nx = 12L, ny = 8L, pitch_len = 105, pitch_wid = 68) {
  x    <- pmin(pmax(as.numeric(x), 0), pitch_len)
  y    <- pmin(pmax(as.numeric(y), 0), pitch_wid)
  xi   <- pmin(floor(x / (pitch_len / nx)) + 1L, nx)
  yi   <- pmin(floor(y / (pitch_wid / ny)) + 1L, ny)
  (yi - 1L) * nx + xi
}

# Build zone-to-zone Gaussian smoothing matrix M (K x K)
build_M <- function(nx = 12L, ny = 8L, pitch_len = 105, pitch_wid = 68, sigma = 8) {
  z       <- seq_len(nx * ny)
  centers <- data.table(
    zone = z,
    x    = ((z - 1L) %% nx + 0.5) * (pitch_len / nx),
    y    = ((z - 1L) %/% nx + 0.5) * (pitch_wid / ny)
  )
  X  <- as.matrix(centers[, .(x, y)])
  d2 <- outer(X[,1], X[,1], "-")^2 + outer(X[,2], X[,2], "-")^2
  W  <- exp(-d2 / (2 * sigma^2))
  W / rowSums(W)
}

# Add possession ID and within-possession sequence number to the actions table
add_possession_and_seq <- function(df) {
  setorderv(df, c("game_id","period_id","time_seconds","action_id"))

  poss_candidates <- c("possession_id","PossessionId","possession","Posesion_id","PosesionId")
  poss_hit        <- poss_candidates[poss_candidates %in% names(df)]

  if (length(poss_hit) > 0) {
    df[, possId := .GRP, by = .(game_id, period_id, get(poss_hit[1]))]
  } else {
    df[, possId := {
      change    <- (team_id != shift(team_id)) | (period_id != shift(period_id))
      change[1] <- TRUE
      cumsum(fifelse(is.na(change), TRUE, change))
    }, by = game_id]
  }
  df[, seq_poss := seq_len(.N), by = .(game_id, possId)]
  invisible(df)
}

# Ensure all zone columns are present in a wide table (fill missing with 0)
ensure_zone_cols <- function(dt_wide, zone_cols) {
  miss  <- setdiff(zone_cols, names(dt_wide))
  if (length(miss) > 0) dt_wide[, (miss) := 0]
  front <- setdiff(names(dt_wide), zone_cols)
  setcolorder(dt_wide, c(front, zone_cols))
  dt_wide
}

# Weighted mode: returns the category with highest total weight
weighted_mode <- function(x, w) {
  x  <- as.character(x)
  ok <- !is.na(x) & nzchar(x) & is.finite(w) & w > 0
  x  <- x[ok]; w <- w[ok]
  if (length(x) == 0) return(NA_character_)
  s  <- tapply(w, x, sum)
  names(s)[which.max(s)]
}

# ============================================================
# 3) LOAD ACTIONS (VAEP) FROM ALL LEAGUES AND STANDARDISE NAMES
# ============================================================
actions_files <- Sys.glob(file.path(vaep_dir, "actions_vaep_*.csv"))
if (length(actions_files) == 0)
  stop("No actions_vaep_*.csv files found in: ", vaep_dir)
cat("\nFound", length(actions_files), "VAEP actions file(s):\n")
for (f in actions_files) cat(" ", basename(f), "\n")

season_candidates    <- c("season","Season","Temporada","season_name","season_id")
poss_candidates      <- c("possession_id","PossessionId","possession","Posesion_id","PosesionId")
team_name_candidates <- c("team_name","teamName","team_name_home","nombre_equipo","Equipo","club")

load_one_actions_file <- function(fp) {
  lc  <- toupper(gsub("^.*actions_vaep_([^.]+)\\.csv$", "\\1", basename(fp)))
  hdr <- names(fread(fp, nrows = 0, showProgress = FALSE))

  season_col <- (season_candidates[season_candidates %in% hdr])[1]
  if (is.na(season_col)) stop("No season column in: ", fp)

  need_cols <- c("game_id","period_id","time_seconds","action_id",
                 "team_id","player_name","receiver_player_name",
                 "start_x","start_y","end_x","end_y",
                 "type_name","vaep_value", season_col)
  poss_hit <- poss_candidates[poss_candidates %in% hdr]
  if (length(poss_hit) > 0) need_cols <- c(need_cols, poss_hit[1])
  tn_hit <- team_name_candidates[team_name_candidates %in% hdr]
  if (length(tn_hit) > 0) need_cols <- c(need_cols, tn_hit[1])

  dt <- fread(fp, select = intersect(need_cols, hdr), showProgress = FALSE)
  setDT(dt)
  setnames(dt, season_col, "season")
  dt[, league_code := lc]
  dt
}

df_list <- lapply(actions_files, load_one_actions_file)
df      <- rbindlist(df_list, fill = TRUE, use.names = TRUE)
rm(df_list)

df[, season        := norm_season(season)]
df[, game_id       := as.character(game_id)]
df[, team_id       := as.character(team_id)]
df[, actor_name    := std_name(player_name)]
df[, receiver_name := std_name(receiver_player_name)]
df[, type_clean    := std_name(type_name, strip_accents = FALSE)]

team_name_col <- team_name_candidates[team_name_candidates %in% names(df)]

assert_has_cols(df,
  c("game_id","period_id","time_seconds","action_id",
    "team_id","player_name","receiver_player_name",
    "start_x","start_y","end_x","end_y",
    "type_name","vaep_value","season","league_code"),
  "actions df"
)

check_coords_105x68_or_stop(df, pitch_len = PITCH_LEN, pitch_wid = PITCH_WID, tol = 0.5)
add_possession_and_seq(df)
df[, zone_recv := zone_id(end_x, end_y, nx, ny, PITCH_LEN, PITCH_WID)]

cat("\n--- ACTIONS LOADED (ALL LEAGUES) ---\n")
cat("Total rows:", nrow(df), "\n")
print(df[, .N, by = .(league_code, season)][order(league_code, season)])

# ============================================================
# 4) PLAYER-SEASON AVERAGE ACTION POSITION
# ============================================================
df[, action_x := fifelse(is.finite(start_x), start_x, fifelse(is.finite(end_x), end_x, NA_real_))]
df[, action_y := fifelse(is.finite(start_y), start_y, fifelse(is.finite(end_y), end_y, NA_real_))]

# Substitutions carry a placeholder corner coordinate; exclude from spatial aggregates
NON_SPATIAL_TYPES <- c("substitution_in", "substitution_out")
df[, is_spatial := !(type_clean %in% NON_SPATIAL_TYPES)]
cat("\n--- NON-SPATIAL ACTION FILTER ---\n")
cat("Rows flagged non-spatial:", sum(!df$is_spatial), "of", nrow(df),
    sprintf("(%.2f%%)\n", 100 * mean(!df$is_spatial)))

player_season_avgpos <- df[
  is_spatial & !is.na(season) & !is.na(actor_name) & is.finite(action_x) & is.finite(action_y),
  .(
    avg_action_x = mean(action_x, na.rm = TRUE),
    avg_action_y = mean(action_y, na.rm = TRUE),
    n_actions    = .N
  ),
  by = .(season, player_name = actor_name)
]
setkey(player_season_avgpos, season, player_name)

cat("\n--- AVG ACTION POSITION DIAGNOSTICS ---\n")
cat("Rows (player_season_avgpos):", nrow(player_season_avgpos), "\n")
cat("Missing avg_action_x:",       sum(is.na(player_season_avgpos$avg_action_x)), "\n")
cat("Missing avg_action_y:",       sum(is.na(player_season_avgpos$avg_action_y)), "\n")

# ============================================================
# 4.1) PLAYER-SEASON ACTION ZONE DISTRIBUTIONS
# ============================================================
df[, action_zone := zone_id(action_x, action_y, nx, ny, PITCH_LEN, PITCH_WID)]

player_season_zone_dist <- df[
  is_spatial & !is.na(season) & !is.na(actor_name) & is.finite(action_x) & is.finite(action_y),
  .N,
  by = .(season, player_name = actor_name, zone = action_zone)
]
player_season_zone_dist[, prob := N / sum(N), by = .(season, player_name)]
player_season_zone_dist[, N := NULL]
setkey(player_season_zone_dist, season, player_name, zone)

cat("\n--- ACTION ZONE DISTRIBUTION DIAGNOSTICS ---\n")
cat("Player-season-zone rows:", nrow(player_season_zone_dist), "\n")
cat("Unique player-seasons:  ", uniqueN(player_season_zone_dist[, .(season, player_name)]), "\n")

# ============================================================
# 5) PLAYER-SEASON VAEP TOTALS (actor only)
# ============================================================
vaep_by_season_player <- df[
  !is.na(season) & !is.na(actor_name) & is.finite(vaep_value),
  .(vaep_total = sum(vaep_value, na.rm = TRUE)),
  by = .(season, player_name = actor_name)
]
setkey(vaep_by_season_player, season, player_name)

# ============================================================
# 6) MINUTES AND POSITIONS FROM PREPROCESSED EVENT STREAM
# ============================================================
event_time_min <- function(minute, second) {
  suppressWarnings(as.numeric(minute)) + suppressWarnings(as.numeric(second)) / 60
}

detect_position_col <- function(nms) {
  cand <- c("position","Position","posicion","Posicion","pos","Pos","position_name",
            "PositionName","posicion_name","PosicionName","posName","positionCode","PositionCode")
  hit  <- cand[cand %in% nms]
  if (length(hit) == 0) return(NA_character_)
  hit[1]
}

build_minutes_positions_one_preprocessed <- function(fp, season_override = NULL) {
  dt <- fread(fp, showProgress = FALSE)
  setDT(dt)

  need_base <- c("matchId","teamId","playerId","jugador","minute","second","event_name","cardType","Temporada")
  miss      <- setdiff(need_base, names(dt))
  if (length(miss) > 0) stop("Missing columns in ", fp, ": ", paste(miss, collapse = ", "))

  pos_col <- detect_position_col(names(dt))
  if (is.na(pos_col))
    stop("No position column detected in ", fp, ".\n",
         "Expected something like 'position'/'posicion'/'position_name'.\n",
         "Columns found: ", paste(head(names(dt), 40), collapse = ", "), " ...")

  dt[, season     := if (!is.null(season_override)) season_override else Temporada]
  dt[, season     := norm_season(season)]
  dt[, player_name := std_name(jugador)]
  dt <- dt[!is.na(player_name) & !is.na(matchId) & !is.na(teamId) & !is.na(playerId)]

  dt[, t_min := event_time_min(minute, second)]
  dt <- dt[is.finite(t_min)]

  dt[, pos_raw   := as.character(get(pos_col))]
  dt[, pos_clean := stringi::stri_trim_both(pos_raw)]
  dt[pos_clean %in% c("","NA","NaN","null"), pos_clean := NA_character_]
  dt[, pos_clean := toupper(pos_clean)]
  dt[pos_clean == "SUB", pos_clean := NA_character_]

  match_end <- dt[, .(match_end_min = max(t_min, na.rm = TRUE)), by = .(season, matchId)]
  setkey(match_end, season, matchId)

  sub_on  <- dt[event_name == "SubstitutionOn",
                .(on_min  = min(t_min, na.rm = TRUE)),
                by = .(season, matchId, teamId, playerId, player_name)]
  sub_off <- dt[event_name == "SubstitutionOff",
                .(off_min = min(t_min, na.rm = TRUE)),
                by = .(season, matchId, teamId, playerId, player_name)]
  red     <- dt[event_name == "Card" & grepl("Red|SecondYellow", cardType, ignore.case = TRUE),
                .(red_min = min(t_min, na.rm = TRUE)),
                by = .(season, matchId, teamId, playerId, player_name)]

  players_seen <- unique(dt[, .(season, matchId, teamId, playerId, player_name)])
  setkey(players_seen, season, matchId, teamId, playerId, player_name)
  setkey(sub_on,  season, matchId, teamId, playerId, player_name)
  setkey(sub_off, season, matchId, teamId, playerId, player_name)
  setkey(red,     season, matchId, teamId, playerId, player_name)

  players_seen[sub_on,  on_min         := i.on_min]
  players_seen[sub_off, off_min        := i.off_min]
  players_seen[red,     red_min        := i.red_min]
  players_seen[match_end, match_end_min := i.match_end_min, on = .(season, matchId)]

  players_seen[is.na(on_min),  on_min  := 0]
  players_seen[is.na(off_min), off_min := match_end_min]
  players_seen[!is.na(red_min), off_min := pmin(off_min, red_min)]
  players_seen[, minutes_played := pmax(off_min - on_min, 0)]

  # Mode position per match-player (excluding Sub/NA)
  pos_mp   <- dt[!is.na(pos_clean), .N, by = .(season, matchId, teamId, playerId, player_name, pos_clean)]
  pos_mp   <- pos_mp[order(-N)]
  pos_mode <- pos_mp[, .SD[1], by = .(season, matchId, teamId, playerId, player_name)]
  pos_mode <- pos_mode[, .(season, matchId, teamId, playerId, player_name, match_pos = pos_clean)]
  setkey(pos_mode, season, matchId, teamId, playerId, player_name)
  players_seen[pos_mode, match_pos := i.match_pos]

  players_seen[, .(
    season, matchId, teamId, playerId, player_name,
    on_min, off_min, match_end_min, minutes_played, match_pos
  )]
}

pre_files <- unlist(lapply(pre_base_dirs, function(d) {
  if (!dir.exists(d)) return(character(0))
  list.files(d, pattern = "^preprocessed_.*\\.csv$", full.names = TRUE, recursive = TRUE)
}))

if (length(pre_files) > 0) {
  cat("\nFound", length(pre_files), "preprocessed event-stream file(s) — computing exact minutes.\n")
  minutes_pos_by_match_player <- rbindlist(
    lapply(pre_files, build_minutes_positions_one_preprocessed),
    fill = TRUE
  )
} else {
  # Fallback: estimate minutes from first-to-last action per game period
  cat("\nNo preprocessed event-stream files found. Estimating minutes from VAEP actions.\n")
  time_col <- if ("time_seconds_overall" %in% names(df)) "time_seconds_overall" else "time_seconds"

  game_period_end <- df[is.finite(get(time_col)),
    .(period_end = max(get(time_col))),
    by = .(season, game_id, period_id)]

  player_pgp <- df[!is.na(actor_name) & is.finite(get(time_col)),
    .(t_first = min(get(time_col)), t_last = max(get(time_col))),
    by = .(season, game_id, period_id, player_name = actor_name)]

  player_pgp[game_period_end, period_end := i.period_end, on = .(season, game_id, period_id)]
  player_pgp[, min_est := fifelse(
    is.finite(period_end) & period_end > 0,
    pmin((t_last - t_first) / period_end * 45, 45),
    0
  )]

  minutes_est_by_season_player <- player_pgp[,
    .(minutes_played = sum(min_est, na.rm = TRUE)),
    by = .(season, player_name)
  ]

  minutes_pos_by_match_player <- player_pgp[, .(
    season, matchId = game_id, teamId = NA_character_,
    playerId = NA_character_, player_name,
    on_min = 0, off_min = t_last / 60, match_end_min = period_end / 60,
    minutes_played = min_est, match_pos = NA_character_
  )]
}

if (exists("minutes_est_by_season_player")) {
  minutes_by_season_player <- minutes_est_by_season_player
  rm(minutes_est_by_season_player)
} else {
  minutes_by_season_player <- minutes_pos_by_match_player[
    , .(minutes_played = sum(minutes_played, na.rm = TRUE)),
    by = .(season, player_name)
  ]
}
setkey(minutes_by_season_player, season, player_name)

# Season-player mode position, weighted by minutes played
player_season_position <- minutes_pos_by_match_player[
  !is.na(match_pos) & match_pos != "SUB",
  .(mode_position = weighted_mode(match_pos, minutes_played)),
  by = .(season, player_name)
]
setkey(player_season_position, season, player_name)

stopifnot(all(c("season","player_name","mode_position") %in% names(player_season_position)))

player_season_position <- merge(
  minutes_by_season_player[, .(season, player_name)],
  player_season_position,
  by  = c("season","player_name"),
  all.x = TRUE
)

player_season_position[mode_position == "Sub", mode_position := NA_character_]
player_season_position[is.na(mode_position) | mode_position == "", mode_position := "MC"]

if (any(player_season_position$mode_position == "Sub", na.rm = TRUE))
  stop("BUG: Found 'SUB' in player_season_position$mode_position.")

cat("\n--- POSITION FILL DIAGNOSTICS ---\n")
cat("Season-player rows (minutes):",           nrow(minutes_by_season_player), "\n")
cat("Season-player rows (positions after fill):", nrow(player_season_position), "\n")
cat("Missing positions after fill:",           player_season_position[is.na(mode_position), .N], "\n")

poscheck        <- merge(minutes_by_season_player, player_season_position, by = c("season","player_name"), all.x = TRUE)
n_missing_pos   <- poscheck[minutes_played > 0 & is.na(mode_position), .N]
if (n_missing_pos > 0) {
  print(poscheck[minutes_played > 0 & is.na(mode_position)][1:20, .(season, player_name, minutes_played)])
  stop("Position missing for ", n_missing_pos, " season-player rows with minutes_played>0.")
}

cat("\n--- MINUTES/POSITION DIAGNOSTICS ---\n")
cat("Player-match rows:",          nrow(minutes_pos_by_match_player), "\n")
cat("Season-player minutes rows:", nrow(minutes_by_season_player), "\n")
cat("Season-player position rows:", nrow(player_season_position), "\n")

# ============================================================
# 7) PLAYER-SEASON VAEP/90 (uses minutes from preprocessed stream)
# ============================================================
player_season_vaep90 <- merge(
  minutes_by_season_player,
  vaep_by_season_player,
  by    = c("season","player_name"),
  all.x = TRUE
)
player_season_vaep90[is.na(vaep_total), vaep_total := 0]
player_season_vaep90[, vaep_per90 := fifelse(
  minutes_played > 0,
  90 * vaep_total / minutes_played,
  NA_real_
)]
setkey(player_season_vaep90, season, player_name)

cat("\n--- VAEP/90 DIAGNOSTICS ---\n")
cat("Rows:", nrow(player_season_vaep90), "\n")
cat("Missing vaep_per90:", sum(is.na(player_season_vaep90$vaep_per90)), "\n")

# ============================================================
# 8) PASS TABLE (feeds Da and Rv distributions)
# ============================================================
passes <- df[
  type_clean %in% PASS_TYPES &
    !is.na(season) & !is.na(game_id) & !is.na(team_id) &
    !is.na(possId) & !is.na(seq_poss) &
    !is.na(actor_name) & !is.na(receiver_name) &
    !is.na(zone_recv),
  .(season, game_id, team_id, possId, seq_poss,
    passer_name   = actor_name,
    receiver_name = receiver_name,
    start_x, start_y, end_x, end_y,
    zone_recv)
]

passes[, w := 1.0]

# ============================================================
# 9) PLAYER PASS VECTORS (PROGRESS / WIDTH DECOMPOSITION)
# ============================================================
passes[, `:=`(pass_dx = end_x - start_x, pass_dy = end_y - start_y)]

pass_given_vec <- passes[
  is.finite(pass_dx) & is.finite(pass_dy),
  {
    dxm <- mean(pass_dx, na.rm = TRUE)
    dym <- mean(pass_dy, na.rm = TRUE)
    list(
      pass_given_dx        = dxm,
      pass_given_dy        = dym,
      pass_given_prog      = dxm,
      pass_given_width_abs = mean(abs(pass_dy), na.rm = TRUE),
      n_passes_out         = .N
    )
  },
  by = .(season, player_name = passer_name)
]
setkey(pass_given_vec, season, player_name)

pass_received_vec <- passes[
  is.finite(pass_dx) & is.finite(pass_dy),
  {
    ws  <- sum(w, na.rm = TRUE)
    dxw <- fifelse(ws > 0, sum(pass_dx * w, na.rm = TRUE) / ws, NA_real_)
    dyw <- fifelse(ws > 0, sum(pass_dy * w, na.rm = TRUE) / ws, NA_real_)
    wab <- fifelse(ws > 0, sum(abs(pass_dy) * w, na.rm = TRUE) / ws, NA_real_)
    list(
      pass_recv_w_sum       = ws,
      pass_recv_dx_w        = dxw,
      pass_recv_dy_w        = dyw,
      pass_recv_prog_w      = dxw,
      pass_recv_width_abs_w = wab,
      n_passes_in           = .N
    )
  },
  by = .(season, player_name = receiver_name)
]
setkey(pass_received_vec, season, player_name)

cat("\n--- PASS VECTOR DIAGNOSTICS ---\n")
cat("Rows (pass_given_vec):",   nrow(pass_given_vec), "\n")
cat("Rows (pass_received_vec):", nrow(pass_received_vec), "\n")

# ============================================================
# 10) AVERAGE PASS ORIGIN / DESTINATION LOCATIONS
# ============================================================
pass_given_xy <- passes[
  is.finite(start_x) & is.finite(start_y) & is.finite(end_x) & is.finite(end_y),
  .(
    pass_out_start_x = mean(start_x, na.rm = TRUE),
    pass_out_start_y = mean(start_y, na.rm = TRUE),
    pass_out_end_x   = mean(end_x,   na.rm = TRUE),
    pass_out_end_y   = mean(end_y,   na.rm = TRUE),
    n_passes_out_xy  = .N
  ),
  by = .(season, player_name = passer_name)
]
setkey(pass_given_xy, season, player_name)

pass_received_xy <- passes[
  is.finite(start_x) & is.finite(start_y) & is.finite(end_x) & is.finite(end_y),
  {
    ws <- sum(w, na.rm = TRUE)
    list(
      pass_in_end_x    = mean(end_x, na.rm = TRUE),
      pass_in_end_y    = mean(end_y, na.rm = TRUE),
      pass_in_end_x_w  = fifelse(ws > 0, sum(end_x * w, na.rm = TRUE) / ws, NA_real_),
      pass_in_end_y_w  = fifelse(ws > 0, sum(end_y * w, na.rm = TRUE) / ws, NA_real_),
      pass_in_w_sum_xy = ws,
      n_passes_in_xy   = .N
    )
  },
  by = .(season, player_name = receiver_name)
]
setkey(pass_received_xy, season, player_name)

cat("\n--- PASS AVG XY DIAGNOSTICS ---\n")
cat("Rows (pass_given_xy):",   nrow(pass_given_xy), "\n")
cat("Rows (pass_received_xy):", nrow(pass_received_xy), "\n")

# ============================================================
# 11) Da AND Rv ZONE DISTRIBUTIONS (player-season level)
# ============================================================
Da_long <- passes[, .N, by = .(season, passer_name, zone = zone_recv)]
Da_long[, total_passes := sum(N), by = .(season, passer_name)]
Da_long[, D := N / total_passes]
Da_long[, c("N","total_passes") := NULL]

Rv_long <- passes[, .(w_sum = sum(w, na.rm = TRUE)), by = .(season, receiver_name, zone = zone_recv)]
Rv_long[, total_w    := sum(w_sum, na.rm = TRUE), by = .(season, receiver_name)]
Rv_long[, rv_defined := (total_w > 0)]
Rv_long[, Rv         := fifelse(total_w > 0, w_sum / total_w, NA_real_)]
Rv_long[, w_sum      := NULL]

Da_wide <- dcast(Da_long, season + passer_name   ~ zone, value.var = "D",  fill = 0)
Rv_wide <- dcast(Rv_long, season + receiver_name ~ zone, value.var = "Rv", fill = 0)
Da_wide <- ensure_zone_cols(Da_wide, zone_cols)
Rv_wide <- ensure_zone_cols(Rv_wide, zone_cols)

Rv_defined <- unique(Rv_long[, .(season, receiver_name, rv_defined, total_w)])
setkey(Da_wide,    season)
setkey(Rv_wide,    season)
setkey(Rv_defined, season, receiver_name)

M <- build_M(nx, ny, PITCH_LEN, PITCH_WID, sigma = SIGMA_M)

Da_plot_long <- copy(Da_long); Da_plot_long[, zone := as.character(zone)]
Rv_plot_long <- copy(Rv_long); Rv_plot_long[, zone := as.character(zone)]

# ============================================================
# 11b) PRIOR-SEASON ROLE PROFILES
# ============================================================

# Map SPADL game_id to event-stream matchId by Jaccard overlap of player sets
JACCARD_MIN <- 0.60

game_players <- unique(df[!is.na(actor_name) & !is.na(season),
                          .(season, game_id = as.character(game_id), player = actor_name)])
match_players <- unique(minutes_pos_by_match_player[!is.na(player_name) & !is.na(season),
                          .(season, mid = as.character(matchId), player = player_name)])
sizes_g <- game_players[,  .(ng = .N), by = .(season, game_id)]
sizes_m <- match_players[, .(nm = .N), by = .(season, mid)]

gid2mid <- rbindlist(lapply(sort(unique(game_players$season)), function(sn) {
  g <- game_players[season == sn]; m <- match_players[season == sn]
  if (nrow(g) == 0 || nrow(m) == 0) return(NULL)
  sh <- merge(g, m, by = c("season", "player"), allow.cartesian = TRUE)[
          , .(n_shared = .N), by = .(season, game_id, mid)]
  if (nrow(sh) == 0) return(NULL)
  sh[sizes_g, ng := i.ng, on = .(season, game_id)]
  sh[sizes_m, nm := i.nm, on = .(season, mid)]
  sh[, jac := n_shared / (ng + nm - n_shared)]
  setorder(sh, season, game_id, -jac)
  sh[, .SD[1], by = .(season, game_id)][jac >= JACCARD_MIN, .(season, game_id, mid, jac)]
}), fill = TRUE)

cat("\n--- MATCH-ID RECOVERY (game_id <-> matchId) ---\n")
cat("Games in actions:", nrow(sizes_g), "| mapped:", nrow(gid2mid),
    sprintf("(%.1f%%)\n", 100 * nrow(gid2mid) / max(1, nrow(sizes_g))))
if (nrow(gid2mid) > 0)
  cat("Median Jaccard of accepted matches:", round(median(gid2mid$jac), 3), "\n")
setkey(gid2mid, season, game_id)

match_pos_lookup <- unique(
  minutes_pos_by_match_player[
    !is.na(match_pos) & match_pos != "" & toupper(match_pos) != "SUB",
    .(season, mid = as.character(matchId), player_name, match_pos = toupper(match_pos))
  ]
)
setkey(match_pos_lookup, season, mid, player_name)

season_pos_lookup <- unique(
  player_season_position[
    !is.na(mode_position) & mode_position != "" & toupper(mode_position) != "SUB",
    .(season, player_name, season_pos = toupper(mode_position))
  ]
)
setkey(season_pos_lookup, season, player_name)

passes_role <- copy(passes)
passes_role[, game_id := as.character(game_id)]
passes_role[gid2mid, mid := i.mid, on = .(season, game_id)]
passes_role[match_pos_lookup, passer_match_pos   := i.match_pos,
            on = .(season, mid, passer_name   = player_name)]
passes_role[match_pos_lookup, receiver_match_pos := i.match_pos,
            on = .(season, mid, receiver_name = player_name)]
cat("Pass ends resolved by MATCH position: passer",
    sprintf("%.0f%%", 100 * mean(!is.na(passes_role$passer_match_pos))),
    "| receiver", sprintf("%.0f%%\n", 100 * mean(!is.na(passes_role$receiver_match_pos))))
passes_role[season_pos_lookup, passer_season_pos   := i.season_pos,
            on = .(season, passer_name   = player_name)]
passes_role[season_pos_lookup, receiver_season_pos := i.season_pos,
            on = .(season, receiver_name = player_name)]

passes_role[, passer_pos_use   := fifelse(!is.na(passer_match_pos),   passer_match_pos,   passer_season_pos)]
passes_role[, receiver_pos_use := fifelse(!is.na(receiver_match_pos), receiver_match_pos, receiver_season_pos)]
passes_role <- passes_role[
  !is.na(passer_pos_use) & !is.na(receiver_pos_use) &
    passer_pos_use != "SUB" & receiver_pos_use != "SUB"
]

role_levels <- sort(unique(c(
  passes_role$passer_pos_use,
  passes_role$receiver_pos_use,
  toupper(player_season_position$mode_position)
)))
role_levels <- role_levels[!is.na(role_levels) & role_levels != "" & role_levels != "SUB"]
K_role      <- length(role_levels)
if (K_role == 0) stop("No valid role levels found.")

player_season_role_universe <- unique(
  player_season_position[!is.na(mode_position) & mode_position != "", .(season, player_name)]
)

out_counts <- passes_role[, .(n_out_to_role = .N),
                           by = .(season, player_name = passer_name,   other_pos = receiver_pos_use)]
out_totals <- passes_role[, .(n_out_total   = .N),
                           by = .(season, player_name = passer_name)]
out_grid   <- player_season_role_universe[, .(other_pos = role_levels), by = .(season, player_name)]
out_prof   <- merge(out_grid, out_counts, by = c("season","player_name","other_pos"), all.x = TRUE)
out_prof   <- merge(out_prof, out_totals, by = c("season","player_name"), all.x = TRUE)
out_prof[is.na(n_out_to_role), n_out_to_role := 0L]
out_prof[, p_out_to_pos := fifelse(
  !is.na(n_out_total) & n_out_total > 0,
  (n_out_to_role + ROLE_ALPHA / K_role) / (n_out_total + ROLE_ALPHA),
  NA_real_
)]

in_counts <- passes_role[, .(n_in_from_role = .N),
                          by = .(season, player_name = receiver_name, other_pos = passer_pos_use)]
in_totals <- passes_role[, .(n_in_total     = .N),
                          by = .(season, player_name = receiver_name)]
in_grid   <- player_season_role_universe[, .(other_pos = role_levels), by = .(season, player_name)]
in_prof   <- merge(in_grid, in_counts, by = c("season","player_name","other_pos"), all.x = TRUE)
in_prof   <- merge(in_prof, in_totals, by = c("season","player_name"), all.x = TRUE)
in_prof[is.na(n_in_from_role), n_in_from_role := 0L]
in_prof[, p_in_from_pos := fifelse(
  !is.na(n_in_total) & n_in_total > 0,
  (n_in_from_role + ROLE_ALPHA / K_role) / (n_in_total + ROLE_ALPHA),
  NA_real_
)]

# ============================================================
# 11c) PLAYING STYLE TABLES
# ============================================================
style_files_ar <- Sys.glob(file.path(vaep_dir, "scores_of_def_*.csv"))
if (length(style_files_ar) == 0)
  stop("No scores_of_def_*.csv files found in: ", vaep_dir)

dt_style_raw_ar <- rbindlist(lapply(style_files_ar, fread, showProgress = FALSE), fill = TRUE)
dt_style_raw_ar[, team_std   := std_name(equipo)]
dt_style_raw_ar[, season_std := norm_season(temporada)]
dt_style <- dt_style_raw_ar[
  !is.na(team_std) & !is.na(season_std),
  .(team_std, season = season_std,
    off_salida = suppressWarnings(as.numeric(Ofensivo_bloque_SALIDA)),
    off_canal  = suppressWarnings(as.numeric(Ofensivo_bloque_CANAL)),
    off_pos    = suppressWarnings(as.numeric(Ofensivo_bloque_POS)),
    off_poses  = suppressWarnings(as.numeric(Ofensivo_bloque_POSES)))
]
rm(dt_style_raw_ar)
setkey(dt_style, season, team_std)

player_season_team <- df[
  !is.na(actor_name) & !is.na(team_id) & !is.na(season),
  .N,
  by = .(season, player_name = actor_name, team_id)
][order(-N)][, .SD[1], by = .(season, player_name)]
player_season_team <- player_season_team[, .(season, player_name, team_id)]
player_season_team[, team_id_chr := as.character(team_id)]

if (length(team_name_col) > 0 && team_name_col[1] %in% names(df)) {
  team_map_from_actions_ar <- df[
    !is.na(team_id) & !is.na(get(team_name_col[1])),
    .N,
    by = .(team_id_chr = as.character(team_id), team_name = get(team_name_col[1]))
  ][order(-N)][, .SD[1], by = team_id_chr]
  team_map_from_actions_ar[, team_std := std_name(team_name)]
  setkey(team_map_from_actions_ar, team_id_chr)
  player_season_team[team_map_from_actions_ar, team_std := i.team_std, on = .(team_id_chr)]
} else {
  player_season_team[, team_std_try := std_name(team_id_chr)]
  direct_matches_ar <- length(intersect(
    unique(player_season_teamteamstdtry),unique(dtstyleteam_std)
  ))
  if (direct_matches_ar >= 5) {
    player_season_team[, team_std := team_std_try]
  } else if (file.exists(team_map_path)) {
    team_map_ar <- fread(team_map_path)
    team_map_ar[, team_id_chr := as.character(team_id)]
    team_map_ar[, team_std    := std_name(team_name)]
    setkey(team_map_ar, team_id_chr)
    player_season_team[team_map_ar, team_std := i.team_std, on = .(team_id_chr)]
  } else {
    stop("Cannot resolve team names for style. Supply a mapping at:\n  ", team_map_path)
  }
}
player_season_team <- player_season_team[, .(season, player_name, team_std)]
setkey(player_season_team, season, player_name)

off_sub_cols <- c("off_salida","off_canal","off_pos","off_poses")
player_season_style <- merge(
  player_season_team,
  dt_style,
  by    = c("season","team_std"),
  all.x = TRUE
)
player_season_style <- player_season_style[, c(list(season = season, player_name = player_name),
                                               .SD), .SDcols = off_sub_cols]
setkey(player_season_style, season, player_name)

# ============================================================
# TRANSFERMARKT SCRAPING HELPERS
# ============================================================
TM_BASE <- "https://www.transfermarkt.us"
TM_UA   <- paste0(
  "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) ",
  "AppleWebKit/537.36 (KHTML, like Gecko) ",
  "Chrome/124.0.0.0 Safari/537.36"
)
TM_TIMEOUT  <- 45L
TM_RETRIES  <- 3L

fetch_html <- function(url) {
  for (attempt in seq_len(TM_RETRIES)) {
    res <- tryCatch(
      httr::GET(url,
                httr::user_agent(TM_UA),
                httr::add_headers(
                  "Accept"          = "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8",
                  "Accept-Language" = "en-US,en;q=0.9",
                  "Accept-Encoding" = "gzip, deflate, br",
                  "Referer"         = paste0(TM_BASE, "/"),
                  "DNT"             = "1",
                  "Connection"      = "keep-alive"
                ),
                httr::config(followlocation = 1L),
                httr::timeout(TM_TIMEOUT)),
      error = function(e) {
        message(sprintf("    attempt %d error: %s", attempt, conditionMessage(e))); NULL
      }
    )
    if (!is.null(res) && httr::status_code(res) == 200) {
      txt <- httr::content(res, as = "text", encoding = "UTF-8")
      doc <- tryCatch(rvest::read_html(txt), error = function(e) {
        message(sprintf("    parse error: %s", conditionMessage(e))); NULL
      })
      if (!is.null(doc)) return(doc)
    } else if (!is.null(res)) {
      message(sprintf("    HTTP %d at %s", httr::status_code(res), url))
    }
    if (attempt < TM_RETRIES) Sys.sleep(5 * attempt)
  }
  NULL
}

parse_mv_tm <- function(s) {
  s   <- as.character(s)
  out <- rep(NA_real_, length(s))
  m   <- grepl("m", s, ignore.case = TRUE)
  k   <- grepl("Th\\.|k", s, ignore.case = TRUE) & !m
  out[m] <- suppressWarnings(as.numeric(gsub("[^0-9.]", "", s[m]))) * 1e6
  out[k] <- suppressWarnings(as.numeric(gsub("[^0-9.]", "", s[k]))) * 1e3
  out
}

get_team_urls_tm <- function(league_slug, league_code_tm, start_year) {
  league_url <- sprintf("%s/%s/startseite/wettbewerb/%s/saison_id/%d",
                        TM_BASE, league_slug, league_code_tm, start_year)
  message(sprintf("  league page: %s", league_url))
  doc <- fetch_html(league_url)
  if (is.null(doc)) return(character(0))
  hrefs <- unique(rvest::html_attr(rvest::html_nodes(doc, "a[href*='/startseite/verein/']"), "href"))
  hrefs <- hrefs[grepl("^/[^/]+/startseite/verein/\\d+", hrefs)]
  hrefs <- sub("\\?.*$", "", hrefs)
  ids   <- sub(".*/verein/(\\d+).*", "\\1", hrefs)
  hrefs <- hrefs[!duplicated(ids)]
  hrefs <- sub("/startseite/verein/(\\d+).*", "/startseite/verein/\\1", hrefs)
  sprintf("%s%s/saison_id/%d", TM_BASE, hrefs, start_year)
}

parse_team_page_tm <- function(team_url) {
  doc <- fetch_html(team_url)
  if (is.null(doc)) return(NULL)
  rows <- rvest::html_nodes(doc, "table.items > tbody > tr")
  if (length(rows) == 0)
    rows <- rvest::html_nodes(doc, "div.responsive-table table tbody tr")
  if (length(rows) == 0) return(NULL)

  out_list <- lapply(rows, function(tr) {
    name_node <- rvest::html_nodes(tr, "a.spielprofil_tooltip")
    if (length(name_node) == 0) name_node <- rvest::html_nodes(tr, "td.hauptlink a")
    if (length(name_node) == 0) return(NULL)
    nm <- rvest::html_text(name_node[[1]], trim = TRUE)

    mv_node <- rvest::html_nodes(tr, "td.rechts.hauptlink")
    if (length(mv_node) == 0) {
      tds     <- rvest::html_nodes(tr, "td")
      mv_node <- if (length(tds) >= 1) tds[length(tds)] else NULL
    }
    mv_txt <- if (!is.null(mv_node) && length(mv_node) > 0)
      rvest::html_text(mv_node[[1]], trim = TRUE) else NA_character_

    data.table(player_name = nm, mv_text = mv_txt)
  })

  out <- rbindlist(out_list, fill = TRUE)
  out <- out[!is.na(player_name) & nzchar(player_name)]
  out[, mv_eur := parse_mv_tm(mv_text)]
  unique(out, by = "player_name")
}

# ============================================================
# 12) LOAD JOI PAIRS FROM ALL LEAGUES
# ============================================================
joi_files <- Sys.glob(file.path(vaep_dir, "joi_pairs_*.csv"))
if (length(joi_files) == 0)
  stop("No joi_pairs_*.csv files found in: ", vaep_dir)
cat("\nFound", length(joi_files), "JOI pairs file(s):\n")
for (f in joi_files) cat(" ", basename(f), "\n")

load_one_joi_file <- function(fp) {
  lc  <- toupper(gsub("^.*joi_pairs_([^.]+)\\.csv$", "\\1", basename(fp)))
  dt  <- fread(fp, showProgress = FALSE)
  setDT(dt)
  dt[, league_code := lc]
  dt
}

pairs_all_list <- lapply(joi_files, load_one_joi_file)
pairs_all      <- rbindlist(pairs_all_list, fill = TRUE, use.names = TRUE)
rm(pairs_all_list)

assert_has_cols(pairs_all, c("season","player1_name","player2_name","minutes_together","joi_per90"), "pairs")

pairs_all[, season      := norm_season(season)]
pairs_all[, player1_name := std_name(player1_name)]
pairs_all[, player2_name := std_name(player2_name)]
pairs_all <- pairs_all[!is.na(season) & !is.na(player1_name) & !is.na(player2_name)]

cat("\n--- JOI PAIRS LOADED (ALL LEAGUES) ---\n")
cat("Total pair-season rows:", nrow(pairs_all), "\n")
print(pairs_all[, .N, by = .(league_code, season)][order(league_code, season)])

# Canonicalise pair order (player1 <= player2 alphabetically)
pairs_all[, `:=`(
  a = fifelse(player1_name <= player2_name, player1_name, player2_name),
  b = fifelse(player1_name <= player2_name, player2_name, player1_name)
)]
pairs_all[, `:=`(player1_name = a, player2_name = b)][, c("a","b") := NULL]
pairs_all[, pair_id    := paste(player1_name, player2_name, sep = "___")]
pairs_all[, season_key := as.integer(substr(season, 1, 2))]

first_map <- pairs_all[
  !is.na(season_key) & !is.na(minutes_together) & minutes_together > 0,
  .(first_season_key = min(season_key)),
  by = pair_id
]
setkey(first_map, pair_id)
pairs_all[first_map, is_first_season_together := (season_key == i.first_season_key), on = .(pair_id)]
pairs_all[is.na(is_first_season_together), is_first_season_together := FALSE]

pairs_filt <- pairs_all[!is.na(joi_per90) & !is.na(minutes_together) & minutes_together >= MIN_MINUTES]
pairs_filt[, season_prev := prev_season(season)]

# ============================================================
# 13) PRIOR-SEASON JOINS: VAEP/90, PASS VECTORS, AVG POSITIONS
# ============================================================

# --- 13.1) VAEP/90 ---
vaep90_lookup <- player_season_vaep90[, .(season, player_name, vaep_per90)]
setkey(vaep90_lookup, season, player_name)

p1_vaep <- copy(vaep90_lookup)
setnames(p1_vaep, c("season","player_name","vaep_per90"),
         c("season_prev","player1_name","vaep_per90_prev_p1"))
setkey(p1_vaep, season_prev, player1_name)

p2_vaep <- copy(vaep90_lookup)
setnames(p2_vaep, c("season","player_name","vaep_per90"),
         c("season_prev","player2_name","vaep_per90_prev_p2"))
setkey(p2_vaep, season_prev, player2_name)

pairs_filt[p1_vaep, vaep_per90_prev_p1 := i.vaep_per90_prev_p1, on = .(season_prev, player1_name)]
pairs_filt[p2_vaep, vaep_per90_prev_p2 := i.vaep_per90_prev_p2, on = .(season_prev, player2_name)]

cat("\n--- PRIOR-SEASON VAEP/90 JOIN DIAGNOSTICS ---\n")
cat("Missing p1:", sum(is.na(pairs_filt$vaep_per90_prev_p1)), "\n")
cat("Missing p2:", sum(is.na(pairs_filt$vaep_per90_prev_p2)), "\n")

# --- 13.2) Pass vectors (progress/width) ---
pass_given_lookup <- pass_given_vec[, .(season, player_name,
  pass_given_dx, pass_given_dy, pass_given_prog, pass_given_width_abs)]
setkey(pass_given_lookup, season, player_name)

pass_recv_lookup <- pass_received_vec[, .(season, player_name,
  pass_recv_dx_w, pass_recv_dy_w, pass_recv_w_sum, pass_recv_prog_w, pass_recv_width_abs_w)]
setkey(pass_recv_lookup, season, player_name)

p1_pg <- copy(pass_given_lookup)
setnames(p1_pg,
  c("season","player_name","pass_given_dx","pass_given_dy","pass_given_prog","pass_given_width_abs"),
  c("season_prev","player1_name","pass_given_dx_prev_p1","pass_given_dy_prev_p1",
    "pass_given_prog_prev_p1","pass_given_width_abs_prev_p1"))
setkey(p1_pg, season_prev, player1_name)

p2_pg <- copy(pass_given_lookup)
setnames(p2_pg,
  c("season","player_name","pass_given_dx","pass_given_dy","pass_given_prog","pass_given_width_abs"),
  c("season_prev","player2_name","pass_given_dx_prev_p2","pass_given_dy_prev_p2",
    "pass_given_prog_prev_p2","pass_given_width_abs_prev_p2"))
setkey(p2_pg, season_prev, player2_name)

p1_pr <- copy(pass_recv_lookup)
setnames(p1_pr,
  c("season","player_name","pass_recv_dx_w","pass_recv_dy_w","pass_recv_w_sum","pass_recv_prog_w","pass_recv_width_abs_w"),
  c("season_prev","player1_name","pass_recv_dx_w_prev_p1","pass_recv_dy_w_prev_p1",
    "pass_recv_w_sum_prev_p1","pass_recv_prog_w_prev_p1","pass_recv_width_abs_w_prev_p1"))
setkey(p1_pr, season_prev, player1_name)

p2_pr <- copy(pass_recv_lookup)
setnames(p2_pr,
  c("season","player_name","pass_recv_dx_w","pass_recv_dy_w","pass_recv_w_sum","pass_recv_prog_w","pass_recv_width_abs_w"),
  c("season_prev","player2_name","pass_recv_dx_w_prev_p2","pass_recv_dy_w_prev_p2",
    "pass_recv_w_sum_prev_p2","pass_recv_prog_w_prev_p2","pass_recv_width_abs_w_prev_p2"))
setkey(p2_pr, season_prev, player2_name)

pairs_filt[p1_pg, `:=`(
  pass_given_dx_prev_p1        = i.pass_given_dx_prev_p1,
  pass_given_dy_prev_p1        = i.pass_given_dy_prev_p1,
  pass_given_prog_prev_p1      = i.pass_given_prog_prev_p1,
  pass_given_width_abs_prev_p1 = i.pass_given_width_abs_prev_p1
), on = .(season_prev, player1_name)]

pairs_filt[p2_pg, `:=`(
  pass_given_dx_prev_p2        = i.pass_given_dx_prev_p2,
  pass_given_dy_prev_p2        = i.pass_given_dy_prev_p2,
  pass_given_prog_prev_p2      = i.pass_given_prog_prev_p2,
  pass_given_width_abs_prev_p2 = i.pass_given_width_abs_prev_p2
), on = .(season_prev, player2_name)]

pairs_filt[p1_pr, `:=`(
  pass_recv_dx_w_prev_p1        = i.pass_recv_dx_w_prev_p1,
  pass_recv_dy_w_prev_p1        = i.pass_recv_dy_w_prev_p1,
  pass_recv_w_sum_prev_p1       = i.pass_recv_w_sum_prev_p1,
  pass_recv_prog_w_prev_p1      = i.pass_recv_prog_w_prev_p1,
  pass_recv_width_abs_w_prev_p1 = i.pass_recv_width_abs_w_prev_p1
), on = .(season_prev, player1_name)]

pairs_filt[p2_pr, `:=`(
  pass_recv_dx_w_prev_p2        = i.pass_recv_dx_w_prev_p2,
  pass_recv_dy_w_prev_p2        = i.pass_recv_dy_w_prev_p2,
  pass_recv_w_sum_prev_p2       = i.pass_recv_w_sum_prev_p2,
  pass_recv_prog_w_prev_p2      = i.pass_recv_prog_w_prev_p2,
  pass_recv_width_abs_w_prev_p2 = i.pass_recv_width_abs_w_prev_p2
), on = .(season_prev, player2_name)]

cat("\n--- PRIOR-SEASON PASS VECTOR JOIN DIAGNOSTICS ---\n")
cat("Missing p1 pass_given:", sum(is.na(pairs_filtpassgivendxprevp1)|is.na(pairsfiltpass_given_dy_prev_p1)), "\n")
cat("Missing p2 pass_given:", sum(is.na(pairs_filtpassgivendxprevp2)|is.na(pairsfiltpass_given_dy_prev_p2)), "\n")
cat("Missing p1 pass_recv:",  sum(is.na(pairs_filt$pass_recv_dx_w_prev_p1) | is.na(pairs_filt$pass_recv_dy_w_prev_p1)), "\n")
cat("Missing p2 pass_recv:",  sum(is.na(pairs_filt$pass_recv_dx_w_prev_p2) | is.na(pairs_filt$pass_recv_dy_w_prev_p2)), "\n")

# --- 13.2b) Pass dominance: |send_ratio_p1 - send_ratio_p2| ---
dominance_lookup <- merge(
  pass_given_vec[,   .(season, player_name, n_passes_out)],
  pass_received_vec[, .(season, player_name, n_passes_in)],
  by  = c("season", "player_name"),
  all = TRUE
)
dominance_lookup[is.na(n_passes_out), n_passes_out := 0L]
dominance_lookup[is.na(n_passes_in),  n_passes_in  := 0L]
dominance_lookup[, send_ratio := fifelse(
  (n_passes_out + n_passes_in) > 0,
  n_passes_out / (n_passes_out + n_passes_in),
  NA_real_
)]
setkey(dominance_lookup, season, player_name)

p1_dom <- copy(dominance_lookup)
setnames(p1_dom, c("season","player_name","send_ratio"),
                 c("season_prev","player1_name","send_ratio_prev_p1"))
p1_dom[, c("n_passes_out","n_passes_in") := NULL]
setkey(p1_dom, season_prev, player1_name)

p2_dom <- copy(dominance_lookup)
setnames(p2_dom, c("season","player_name","send_ratio"),
                 c("season_prev","player2_name","send_ratio_prev_p2"))
p2_dom[, c("n_passes_out","n_passes_in") := NULL]
setkey(p2_dom, season_prev, player2_name)

pairs_filt[p1_dom, send_ratio_prev_p1 := i.send_ratio_prev_p1, on = .(season_prev, player1_name)]
pairs_filt[p2_dom, send_ratio_prev_p2 := i.send_ratio_prev_p2, on = .(season_prev, player2_name)]
pairs_filt[, pass_dominance_diff_prev := abs(send_ratio_prev_p1 - send_ratio_prev_p2)]

cat("\n--- PASS DOMINANCE DIAGNOSTICS ---\n")
cat("Missing p1 send_ratio:", sum(is.na(pairs_filt$send_ratio_prev_p1)), "\n")
cat("Missing p2 send_ratio:", sum(is.na(pairs_filt$send_ratio_prev_p2)), "\n")
cat("Missing pair diff:",     sum(is.na(pairs_filt$pass_dominance_diff_prev)), "\n")
print(summary(pairs_filt$pass_dominance_diff_prev))

# --- 13.3) Average pass destination locations ---
pass_out_lookup <- pass_given_xy[, .(season, player_name,
  pass_out_start_x, pass_out_start_y, pass_out_end_x, pass_out_end_y, n_passes_out_xy)]
setkey(pass_out_lookup, season, player_name)

pass_in_lookup <- pass_received_xy[, .(season, player_name,
  pass_in_end_x, pass_in_end_y, pass_in_end_x_w, pass_in_end_y_w, pass_in_w_sum_xy, n_passes_in_xy)]
setkey(pass_in_lookup, season, player_name)

p1_out <- copy(pass_out_lookup)
setnames(p1_out,
  c("season","player_name","pass_out_start_x","pass_out_start_y","pass_out_end_x","pass_out_end_y","n_passes_out_xy"),
  c("season_prev","player1_name","pass_out_start_x_prev_p1","pass_out_start_y_prev_p1",
    "pass_out_end_x_prev_p1","pass_out_end_y_prev_p1","n_passes_out_xy_prev_p1"))
setkey(p1_out, season_prev, player1_name)

p2_out <- copy(pass_out_lookup)
setnames(p2_out,
  c("season","player_name","pass_out_start_x","pass_out_start_y","pass_out_end_x","pass_out_end_y","n_passes_out_xy"),
  c("season_prev","player2_name","pass_out_start_x_prev_p2","pass_out_start_y_prev_p2",
    "pass_out_end_x_prev_p2","pass_out_end_y_prev_p2","n_passes_out_xy_prev_p2"))
setkey(p2_out, season_prev, player2_name)

p1_in <- copy(pass_in_lookup)
setnames(p1_in,
  c("season","player_name","pass_in_end_x","pass_in_end_y","pass_in_end_x_w","pass_in_end_y_w","pass_in_w_sum_xy","n_passes_in_xy"),
  c("season_prev","player1_name","pass_in_end_x_prev_p1","pass_in_end_y_prev_p1",
    "pass_in_end_x_w_prev_p1","pass_in_end_y_w_prev_p1","pass_in_w_sum_xy_prev_p1","n_passes_in_xy_prev_p1"))
setkey(p1_in, season_prev, player1_name)

p2_in <- copy(pass_in_lookup)
setnames(p2_in,
  c("season","player_name","pass_in_end_x","pass_in_end_y","pass_in_end_x_w","pass_in_end_y_w","pass_in_w_sum_xy","n_passes_in_xy"),
  c("season_prev","player2_name","pass_in_end_x_prev_p2","pass_in_end_y_prev_p2",
    "pass_in_end_x_w_prev_p2","pass_in_end_y_w_prev_p2","pass_in_w_sum_xy_prev_p2","n_passes_in_xy_prev_p2"))
setkey(p2_in, season_prev, player2_name)

pairs_filt[p1_out, `:=`(
  pass_out_start_x_prev_p1 = i.pass_out_start_x_prev_p1,
  pass_out_start_y_prev_p1 = i.pass_out_start_y_prev_p1,
  pass_out_end_x_prev_p1   = i.pass_out_end_x_prev_p1,
  pass_out_end_y_prev_p1   = i.pass_out_end_y_prev_p1,
  n_passes_out_xy_prev_p1  = i.n_passes_out_xy_prev_p1
), on = .(season_prev, player1_name)]

pairs_filt[p2_out, `:=`(
  pass_out_start_x_prev_p2 = i.pass_out_start_x_prev_p2,
  pass_out_start_y_prev_p2 = i.pass_out_start_y_prev_p2,
  pass_out_end_x_prev_p2   = i.pass_out_end_x_prev_p2,
  pass_out_end_y_prev_p2   = i.pass_out_end_y_prev_p2,
  n_passes_out_xy_prev_p2  = i.n_passes_out_xy_prev_p2
), on = .(season_prev, player2_name)]

pairs_filt[p1_in, `:=`(
  pass_in_end_x_prev_p1    = i.pass_in_end_x_prev_p1,
  pass_in_end_y_prev_p1    = i.pass_in_end_y_prev_p1,
  pass_in_end_x_w_prev_p1  = i.pass_in_end_x_w_prev_p1,
  pass_in_end_y_w_prev_p1  = i.pass_in_end_y_w_prev_p1,
  pass_in_w_sum_xy_prev_p1 = i.pass_in_w_sum_xy_prev_p1,
  n_passes_in_xy_prev_p1   = i.n_passes_in_xy_prev_p1
), on = .(season_prev, player1_name)]

pairs_filt[p2_in, `:=`(
  pass_in_end_x_prev_p2    = i.pass_in_end_x_prev_p2,
  pass_in_end_y_prev_p2    = i.pass_in_end_y_prev_p2,
  pass_in_end_x_w_prev_p2  = i.pass_in_end_x_w_prev_p2,
  pass_in_end_y_w_prev_p2  = i.pass_in_end_y_w_prev_p2,
  pass_in_w_sum_xy_prev_p2 = i.pass_in_w_sum_xy_prev_p2,
  n_passes_in_xy_prev_p2   = i.n_passes_in_xy_prev_p2
), on = .(season_prev, player2_name)]

pairs_filt[, pass_dest_dist_a_to_b :=
             sqrt((pass_out_end_x_prev_p1 - pass_in_end_x_w_prev_p2)^2 +
                    (pass_out_end_y_prev_p1 - pass_in_end_y_w_prev_p2)^2)]
pairs_filt[, pass_dest_dist_b_to_a :=
             sqrt((pass_out_end_x_prev_p2 - pass_in_end_x_w_prev_p1)^2 +
                    (pass_out_end_y_prev_p2 - pass_in_end_y_w_prev_p1)^2)]
pairs_filt[, pass_dest_dist_sum     := pass_dest_dist_a_to_b + pass_dest_dist_b_to_a]

pairs_filt[, pass_dest_comp_a_to_b := 1 / (1 + pass_dest_dist_a_to_b)]
pairs_filt[, pass_dest_comp_b_to_a := 1 / (1 + pass_dest_dist_b_to_a)]
pairs_filt[, pass_dest_comp_sum    := pass_dest_comp_a_to_b + pass_dest_comp_b_to_a]

cat("\n--- PASS DESTINATION DISTANCE DIAGNOSTICS ---\n")
cat("Missing a->b dist:", sum(is.na(pairs_filt$pass_dest_dist_a_to_b)), "\n")
cat("Missing b->a dist:", sum(is.na(pairs_filt$pass_dest_dist_b_to_a)), "\n")
cat("Missing sum dist:",  sum(is.na(pairs_filt$pass_dest_dist_sum)), "\n")

# --- 13.4) Average action positions ---
avgpos_lookup <- player_season_avgpos[, .(season, player_name, avg_action_x, avg_action_y, n_actions)]
setkey(avgpos_lookup, season, player_name)

p1_avgpos <- copy(avgpos_lookup)
setnames(p1_avgpos,
  c("season","player_name","avg_action_x","avg_action_y","n_actions"),
  c("season_prev","player1_name","avg_action_x_prev_p1","avg_action_y_prev_p1","n_actions_prev_p1"))
setkey(p1_avgpos, season_prev, player1_name)

p2_avgpos <- copy(avgpos_lookup)
setnames(p2_avgpos,
  c("season","player_name","avg_action_x","avg_action_y","n_actions"),
  c("season_prev","player2_name","avg_action_x_prev_p2","avg_action_y_prev_p2","n_actions_prev_p2"))
setkey(p2_avgpos, season_prev, player2_name)

pairs_filt[p1_avgpos, `:=`(
  avg_action_x_prev_p1 = i.avg_action_x_prev_p1,
  avg_action_y_prev_p1 = i.avg_action_y_prev_p1,
  n_actions_prev_p1    = i.n_actions_prev_p1
), on = .(season_prev, player1_name)]

pairs_filt[p2_avgpos, `:=`(
  avg_action_x_prev_p2 = i.avg_action_x_prev_p2,
  avg_action_y_prev_p2 = i.avg_action_y_prev_p2,
  n_actions_prev_p2    = i.n_actions_prev_p2
), on = .(season_prev, player2_name)]

pairs_filt[, avg_action_pos_dist_prev := sqrt(
  (avg_action_x_prev_p1 - avg_action_x_prev_p2)^2 +
    (avg_action_y_prev_p1 - avg_action_y_prev_p2)^2
)]

cat("\n--- PRIOR-SEASON AVG ACTION POSITION JOIN DIAGNOSTICS ---\n")
cat("Missing p1 avg pos:", sum(is.na(pairs_filt$avg_action_x_prev_p1) | is.na(pairs_filt$avg_action_y_prev_p1)), "\n")
cat("Missing p2 avg pos:", sum(is.na(pairs_filt$avg_action_x_prev_p2) | is.na(pairs_filt$avg_action_y_prev_p2)), "\n")
cat("Missing pair dist:", sum(is.na(pairs_filt$avg_action_pos_dist_prev)), "\n")

# --- 13.5) Earth Mover's Distance between prior-season action heatmaps ---
compute_prevseason_emd <- function(dt_pairs) {
  sp_list  <- sort(unique(na.omit(dt_pairs$season_prev)))
  out_list <- vector("list", length(sp_list) + 1L)
  idx      <- 0L

  for (sp in sp_list) {
    sub <- dt_pairs[season_prev == sp]
    if (nrow(sub) == 0) next

    zone_data <- player_season_zone_dist[season == sp]
    if (nrow(zone_data) == 0) {
      sub[, action_emd_prev := NA_real_]
      idx <- idx + 1L; out_list[[idx]] <- sub
      next
    }

    players_needed <- unique(c(subplayer1name,subplayer2_name))
    prob_vecs <- lapply(players_needed, function(pname) {
      pd <- zone_data[player_name == pname]
      if (nrow(pd) == 0) return(NULL)
      v        <- rep(0, K)
      v[pdzone]<-pdprob
      v / sum(v)
    })
    names(prob_vecs) <- players_needed

    emd_vals <- vapply(seq_len(nrow(sub)), function(i) {
      a_vec <- prob_vecs[[sub$player1_name[i]]]
      b_vec <- prob_vecs[[sub$player2_name[i]]]
      if (is.null(a_vec) || is.null(b_vec)) return(NA_real_)
      tryCatch(
        wasserstein(wpp(zone_centres_xy, a_vec),
                    wpp(zone_centres_xy, b_vec), p = 1L),
        error = function(e) NA_real_
      )
    }, numeric(1))

    sub[, action_emd_prev := emd_vals]
    idx <- idx + 1L; out_list[[idx]] <- sub
  }

  sub_na <- dt_pairs[is.na(season_prev)]
  if (nrow(sub_na) > 0) {
    sub_na[, action_emd_prev := NA_real_]
    idx <- idx + 1L; out_list[[idx]] <- sub_na
  }
  rbindlist(out_list[seq_len(idx)], fill = TRUE)
}

cat("\nComputing prior-season action EMD for all pairs...\n")
pairs_filt <- compute_prevseason_emd(pairs_filt)

cat("\n--- ACTION EMD DIAGNOSTICS ---\n")
cat("Missing action_emd_prev:", sum(is.na(pairs_filt$action_emd_prev)), "\n")
print(summary(pairs_filt$action_emd_prev))

# ============================================================
# 14) PRIOR-SEASON ZONE COMPATIBILITY (Da * M * Rv, both directions)
# ============================================================
compute_prevseason_compat <- function(dt_pairs) {
  sp_list  <- sort(unique(na.omit(dt_pairs$season_prev)))
  out_list <- vector("list", length(sp_list) + 1L)
  idx      <- 0L

  for (sp in sp_list) {
    sub  <- dt_pairs[season_prev == sp]
    if (nrow(sub) == 0) next

    Da_g <- Da_wide[J(sp)]
    Rv_g <- Rv_wide[J(sp)]
    if (nrow(Da_g) == 0 || nrow(Rv_g) == 0) {
      sub[, `:=`(Da_M_Rv_b_prev = NA_real_, Db_M_Rv_a_prev = NA_real_, compat_sum_prev = NA_real_)]
      idx <- idx + 1L; out_list[[idx]] <- sub
      next
    }

    Da_mat <- as.matrix(Da_g[, ..zone_cols]); rownames(Da_mat) <- Da_g$passer_name
    Rv_mat <- as.matrix(Rv_g[, ..zone_cols]); rownames(Rv_mat) <- Rv_g$receiver_name
    DaM    <- Da_mat %*% M

    valid_receivers <- Rv_defined[J(sp), nomatch = 0][rv_defined == TRUE, receiver_name]

    a <- sub$player1_name
    b <- sub$player2_name

    ia   <- match(a, rownames(DaM))
    ib   <- match(b, rownames(Rv_mat))
    b_ok <- b %in% valid_receivers

    Da_M_Rv_b <- rep(NA_real_, nrow(sub))
    ok_ab     <- !is.na(ia) & !is.na(ib) & b_ok
    if (any(ok_ab))
      Da_M_Rv_b[ok_ab] <- rowSums(DaM[ia[ok_ab], , drop = FALSE] * Rv_mat[ib[ok_ab], , drop = FALSE])

    ia2  <- match(b, rownames(DaM))
    ib2  <- match(a, rownames(Rv_mat))
    a_ok <- a %in% valid_receivers

    Db_M_Rv_a <- rep(NA_real_, nrow(sub))
    ok_ba     <- !is.na(ia2) & !is.na(ib2) & a_ok
    if (any(ok_ba))
      Db_M_Rv_a[ok_ba] <- rowSums(DaM[ia2[ok_ba], , drop = FALSE] * Rv_mat[ib2[ok_ba], , drop = FALSE])

    sub[, `:=`(
      Da_M_Rv_b_prev = Da_M_Rv_b,
      Db_M_Rv_a_prev = Db_M_Rv_a,
      compat_sum_prev = Da_M_Rv_b + Db_M_Rv_a
    )]
    idx <- idx + 1L; out_list[[idx]] <- sub
  }

  sub_na <- dt_pairs[is.na(season_prev)]
  if (nrow(sub_na) > 0) {
    sub_na[, `:=`(Da_M_Rv_b_prev = NA_real_, Db_M_Rv_a_prev = NA_real_, compat_sum_prev = NA_real_)]
    idx <- idx + 1L; out_list[[idx]] <- sub_na
  }

  rbindlist(out_list[seq_len(idx)], fill = TRUE)
}

pairs_filt <- compute_prevseason_compat(pairs_filt)

# ============================================================
# 15) PRIOR-SEASON PRESENCE FLAG (both players in actions DB)
# ============================================================
presence <- unique(rbind(
  df[!is.na(actor_name),    .(season, player = actor_name)],
  df[!is.na(receiver_name), .(season, player = receiver_name)]
))
setkey(presence, season, player)

pairs_filt[, `:=`(p1_in_db_prev = FALSE, p2_in_db_prev = FALSE)]

p1_map <- copy(presence); setnames(p1_map, c("season","player"), c("season_prev","player1_name"))
p2_map <- copy(presence); setnames(p2_map, c("season","player"), c("season_prev","player2_name"))
setkey(p1_map, season_prev, player1_name)
setkey(p2_map, season_prev, player2_name)

pairs_filt[p1_map, p1_in_db_prev := TRUE, on = .(season_prev, player1_name)]
pairs_filt[p2_map, p2_in_db_prev := TRUE, on = .(season_prev, player2_name)]
pairs_filt[, both_in_db_prev_season := (p1_in_db_prev & p2_in_db_prev)]

# ============================================================
# 16) NEW-PAIR FLAG
#     Both players present in the prior season, not yet paired together
# ============================================================
pair_season_exists <- unique(
  pairs_all[!is.na(minutes_together) & minutes_together > 0, .(pair_id, season)]
)
setkey(pair_season_exists, pair_id, season)

pairs_filt[, has_pair_prev_season := FALSE]
pairs_filt[pair_season_exists, has_pair_prev_season := TRUE, on = .(pair_id, season_prev = season)]

pairs_filt[, is_new_pair_season :=
             !is.na(season_prev) &
             both_in_db_prev_season == TRUE &
             has_pair_prev_season == FALSE]

cat("\n--- NEW-PAIR FLAG DIAGNOSTICS ---\n")
cat("Rows in pairs_filt:", nrow(pairs_filt), "\n")
cat("Rows flagged new:",   sum(pairs_filt$is_new_pair_season, na.rm = TRUE), "\n")

# ============================================================
# 17) POSITION DISTANCE (PRIOR SEASON) — theoretical 6x3 grid
# ============================================================
pos_cell <- data.table(
  pos = c("GK",
          "DL","DC","DR",
          "DML","DMC","DMR",
          "ML","MC","MR",
          "AML","AMC","AMR",
          "FWL","FW","FWR"),
  row = c(1, 2,2,2, 3,3,3, 4,4,4, 5,5,5, 6,6,6),
  col = c(2, 1,2,3, 1,2,3, 1,2,3, 1,2,3, 1,2,3)
)
setkey(pos_cell, pos)

pos_alias <- c(
  # Goalkeepers
  "P"    = "GK",  "POR"  = "GK",  "PORT" = "GK",
  # Defenders
  "CB"   = "DC",  "CD"   = "DC",  "D"    = "DC", "CENTRAL DEFENDER CENTRE" = "DC",
  "LB"   = "DL",  "LD"   = "DL",  "LWB"  = "DL",  "LI"   = "DL",
  "RB"   = "DR",  "RD"   = "DR",  "RWB"  = "DR",  "LD2"  = "DR", "WING BACK RIGHT" = "DR",
  # Defensive midfielders
  "DM"   = "DMC", "CDM"  = "DMC", "MDF"  = "DMC", "MD"   = "DMC",
  "LDM"  = "DML", "LCDM" = "DML",
  "RDM"  = "DMR", "RCDM" = "DMR",
  # Central midfielders
  "CM"   = "MC",  "M"    = "MC",  "MF"   = "MC",  "MID"  = "MC",  "CC"  = "MC", "CENTRAL MIDFIELDER LEFT" = "MC", "CENTRAL MIDFIELDER RIGHT" = "MC",
  "LM"   = "ML",  "LCM"  = "ML",
  "RM"   = "MR",  "RCM"  = "MR",
  # Attacking midfielders / wingers
  "CAM"  = "AMC", "AM"   = "AMC", "SS"   = "AMC", "TRQ"  = "AMC", "MEQ" = "AMC",
  "LW"   = "AML", "LAM"  = "AML", "LF"   = "AML", "EI"   = "AML",
  "RW"   = "AMR", "RAM"  = "AMR", "RF"   = "AMR", "ED"   = "AMR",
  # Forwards
  "ST"   = "FW",  "CF"   = "FW",  "F"    = "FW",  "ATT"  = "FW",  "DEL" = "FW", "SECOND STRIKER CENTRE" = "FW", 
  "LWF"  = "FWL", "LST"  = "FWL", "STRIKER LEFT/CENTRE" = "FWL",
  "RWF"  = "FWR", "RST"  = "FWR", "STRIKER CENTRE/RIGHT" = "FWR"
)

resolve_pos <- function(pos_vec) {
  out <- as.character(pos_vec)
  in_alias  <- out %in% names(pos_alias)
  out[in_alias] <- pos_alias[out[in_alias]]
  out
}

pos_lookup <- player_season_position[, .(season, player_name, pos_prev = mode_position)]
setkey(pos_lookup, season, player_name)

p1_pos <- copy(pos_lookup)
setnames(p1_pos, c("season","player_name","pos_prev"), c("season_prev","player1_name","p1_pos_prev"))
setkey(p1_pos, season_prev, player1_name)

p2_pos <- copy(pos_lookup)
setnames(p2_pos, c("season","player_name","pos_prev"), c("season_prev","player2_name","p2_pos_prev"))
setkey(p2_pos, season_prev, player2_name)

pairs_filt[p1_pos, p1_pos_prev := i.p1_pos_prev, on = .(season_prev, player1_name)]
pairs_filt[p2_pos, p2_pos_prev := i.p2_pos_prev, on = .(season_prev, player2_name)]

if (any(pairs_filtp1posprev=="SUB",na.rm=TRUE)||any(pairsfiltp2_pos_prev == "SUB", na.rm = TRUE))
  stop("BUG: 'SUB' appeared in p1_pos_prev/p2_pos_prev.")

pairs_filt[, p1_pos_clean := resolve_pos(toupper(p1_pos_prev))]
pairs_filt[, p2_pos_clean := resolve_pos(toupper(p2_pos_prev))]

known_pos   <- pos_cell$pos
all_pos_in_data <- sort(unique(na.omit(c(pairs_filtp1posclean,pairsfiltp2_pos_clean))))
uncovered   <- setdiff(all_pos_in_data, known_pos)
n_na_p1     <- pairs_filt[is.na(p1_pos_clean), .N]
n_na_p2     <- pairs_filt[is.na(p2_pos_clean), .N]
cat("\n--- POSITION CODE DIAGNOSTIC ---\n")
cat("Known canonical codes (pos_cell):", paste(sort(known_pos), collapse = ", "), "\n")
if (length(uncovered) > 0) {
  cat("UNCOVERED codes still in data (add to pos_alias):", paste(uncovered, collapse = ", "), "\n")
} else {
  cat("All non-NA codes are covered by pos_cell / pos_alias.\n")
}
cat(sprintf("Rows with NA p1_pos_clean: %d  |  NA p2_pos_clean: %d\n", n_na_p1, n_na_p2))
cat("(NA rows = player has no prior-season position record; excluded from model)\n")

p1_cell <- copy(pos_cell); setnames(p1_cell, c("pos","row","col"), c("p1_pos_clean","p1_row","p1_col"))
p2_cell <- copy(pos_cell); setnames(p2_cell, c("pos","row","col"), c("p2_pos_clean","p2_row","p2_col"))
setkey(p1_cell, p1_pos_clean)
setkey(p2_cell, p2_pos_clean)

pairs_filt[p1_cell, `:=`(p1_row = i.p1_row, p1_col = i.p1_col), on = .(p1_pos_clean)]
pairs_filt[p2_cell, `:=`(p2_row = i.p2_row, p2_col = i.p2_col), on = .(p2_pos_clean)]

n_unmapped <- pairs_filt[
  is_new_pair_season == TRUE & (is.na(p1_row) | is.na(p2_row) | is.na(p1_col) | is.na(p2_col)), .N]
if (n_unmapped > 0) {
  unknown_codes <- unique(c(
    pairs_filt[is_new_pair_season == TRUE & (is.na(p1_row) | is.na(p1_col)), p1_pos_clean],
    pairs_filt[is_new_pair_season == TRUE & (is.na(p2_row) | is.na(p2_col)), p2_pos_clean]
  ))
  unknown_codes <- sort(na.omit(unknown_codes))
  if (length(unknown_codes) > 0) {
    cat(sprintf("\nWARNING: %d new-pair rows have unrecognised position codes: %s\n",
                n_unmapped, paste(unknown_codes, collapse = ", ")))
    cat("Add any missing codes to pos_alias in Section 17 to cover them.\n")
  } else {
    cat(sprintf("\nNOTE: %d new-pair rows have no prior-season position recorded.",
                n_unmapped))
    cat(" position_distance_prev will be NA for these pairs; they are excluded from the model.\n")
  }
}

pairs_filt[, position_distance_prev := sqrt((p1_row - p2_row)^2 + (p1_col - p2_col)^2)]

cat("\n--- POSITION DISTANCE DIAGNOSTICS ---\n")
cat("Non-NA position_distance_prev:", sum(is.finite(pairs_filt$position_distance_prev)), "\n")
print(summary(pairs_filt$position_distance_prev))

# ============================================================
# 18) PRIOR-SEASON ROLE-MATCH SCORE
#     role_match_ab_prev = sqrt( P(a->b_role) * P(b<-a_role) )
# ============================================================
p1_out_role <- copy(out_prof)[, .(season_prev = season, player1_name = player_name,
                                   p2_pos_clean = other_pos, p1_out_to_p2pos_prev = p_out_to_pos)]
setkey(p1_out_role, season_prev, player1_name, p2_pos_clean)

p2_out_role <- copy(out_prof)[, .(season_prev = season, player2_name = player_name,
                                   p1_pos_clean = other_pos, p2_out_to_p1pos_prev = p_out_to_pos)]
setkey(p2_out_role, season_prev, player2_name, p1_pos_clean)

p1_in_role  <- copy(in_prof)[, .(season_prev = season, player1_name = player_name,
                                  p2_pos_clean = other_pos, p1_in_from_p2pos_prev = p_in_from_pos)]
setkey(p1_in_role, season_prev, player1_name, p2_pos_clean)

p2_in_role  <- copy(in_prof)[, .(season_prev = season, player2_name = player_name,
                                  p1_pos_clean = other_pos, p2_in_from_p1pos_prev = p_in_from_pos)]
setkey(p2_in_role, season_prev, player2_name, p1_pos_clean)

pairs_filt[p1_out_role, p1_out_to_p2pos_prev  := i.p1_out_to_p2pos_prev,  on = .(season_prev, player1_name, p2_pos_clean)]
pairs_filt[p2_in_role,  p2_in_from_p1pos_prev := i.p2_in_from_p1pos_prev, on = .(season_prev, player2_name, p1_pos_clean)]
pairs_filt[p2_out_role, p2_out_to_p1pos_prev  := i.p2_out_to_p1pos_prev,  on = .(season_prev, player2_name, p1_pos_clean)]
pairs_filt[p1_in_role,  p1_in_from_p2pos_prev := i.p1_in_from_p2pos_prev, on = .(season_prev, player1_name, p2_pos_clean)]

pairs_filt[, role_match_ab_prev  := sqrt(p1_out_to_p2pos_prev * p2_in_from_p1pos_prev)]
pairs_filt[, role_match_ba_prev  := sqrt(p2_out_to_p1pos_prev * p1_in_from_p2pos_prev)]
pairs_filt[, role_match_sum_prev := role_match_ab_prev + role_match_ba_prev]

cat("\n--- ROLE MATCH DIAGNOSTICS ---\n")
cat("Missing p1_out_to_p2pos_prev:",  sum(is.na(pairs_filt$p1_out_to_p2pos_prev)), "\n")
cat("Missing p2_in_from_p1pos_prev:", sum(is.na(pairs_filt$p2_in_from_p1pos_prev)), "\n")
cat("Missing p2_out_to_p1pos_prev:",  sum(is.na(pairs_filt$p2_out_to_p1pos_prev)), "\n")
cat("Missing p1_in_from_p2pos_prev:", sum(is.na(pairs_filt$p1_in_from_p2pos_prev)), "\n")
cat("Missing role_match_sum_prev:",   sum(is.na(pairs_filt$role_match_sum_prev)), "\n")
print(summary(pairs_filt$role_match_sum_prev))

# ============================================================
# 19) FINAL OUTPUT (filter to target seasons)
# ============================================================
final_pairs_prevseason_filtered <- pairs_filt[season %in% c("23-24","24-25","25-26")]

cat("\n--- OUTPUT DIAGNOSTICS ---\n")
cat("Rows (minutes>=", MIN_MINUTES, "): ", nrow(final_pairs_prevseason_filtered), "\n", sep = "")
cat("Rows flagged new: ",                  sum(final_pairs_prevseason_filtered$is_new_pair_season, na.rm = TRUE), "\n", sep = "")
cat("Rows with compat_sum_prev non-NA: ",  sum(!is.na(final_pairs_prevseason_filtered$compat_sum_prev)), "\n", sep = "")
cat("Rows with posdist non-NA: ",          sum(is.finite(final_pairs_prevseason_filtered$position_distance_prev)), "\n", sep = "")

###############################################################################
# PLOTS (pitch tile visualisations)
###############################################################################
pitch_layers <- function(pitch_len = 105, pitch_wid = 68) {
  goal_w   <- 7.32
  pa_d     <- 16.5
  pa_w     <- 40.32
  ga_d     <- 5.5
  ga_w     <- 18.32
  pen_spot <- 11
  cc_r     <- 9.15
  arc_r    <- 9.15
  corner_r <- 1.0

  pa_ymin   <- (pitch_wid - pa_w)   / 2
  pa_ymax   <- (pitch_wid + pa_w)   / 2
  ga_ymin   <- (pitch_wid - ga_w)   / 2
  ga_ymax   <- (pitch_wid + ga_w)   / 2
  goal_ymin <- (pitch_wid - goal_w) / 2
  goal_ymax <- (pitch_wid + goal_w) / 2

  arc_path <- function(cx, cy, r, theta1, theta2, n = 200) {
    th <- seq(theta1, theta2, length.out = n)
    data.frame(x = cx + r * cos(th), y = cy + r * sin(th))
  }

  midy      <- pitch_wid / 2
  th_left   <- acos((pa_d - pen_spot) / arc_r)
  left_arc  <- arc_path(pen_spot,              midy, arc_r, -th_left,     th_left)
  th_right  <- acos((pa_d - pen_spot) / arc_r)
  right_arc <- arc_path(pitch_len - pen_spot,  midy, arc_r, pi - th_right, pi + th_right)

  list(
    annotate("rect", xmin=0, xmax=pitch_len, ymin=0, ymax=pitch_wid, fill="#2E7D32", color=NA),
    annotate("rect", xmin=0, xmax=pitch_len, ymin=0, ymax=pitch_wid, fill=NA, color="white", linewidth=0.7),
    annotate("segment", x=pitch_len/2, xend=pitch_len/2, y=0, yend=pitch_wid, color="white", linewidth=0.7),
    annotate("path",
             x = pitch_len/2 + cc_r*cos(seq(0, 2*pi, length.out=200)),
             y = pitch_wid/2 + cc_r*sin(seq(0, 2*pi, length.out=200)),
             color="white", linewidth=0.7),
    annotate("point", x=pitch_len/2, y=pitch_wid/2, color="white", size=1.5),
    annotate("rect", xmin=0,              xmax=pa_d,        ymin=pa_ymin, ymax=pa_ymax, fill=NA, color="white", linewidth=0.7),
    annotate("rect", xmin=pitch_len-pa_d, xmax=pitch_len,   ymin=pa_ymin, ymax=pa_ymax, fill=NA, color="white", linewidth=0.7),
    annotate("rect", xmin=0,              xmax=ga_d,        ymin=ga_ymin, ymax=ga_ymax, fill=NA, color="white", linewidth=0.7),
    annotate("rect", xmin=pitch_len-ga_d, xmax=pitch_len,   ymin=ga_ymin, ymax=ga_ymax, fill=NA, color="white", linewidth=0.7),
    annotate("point", x=pen_spot,              y=midy, color="white", size=1.5),
    annotate("point", x=pitch_len - pen_spot,  y=midy, color="white", size=1.5),
    geom_path(data=left_arc,  aes(x=x, y=y), inherit.aes=FALSE, color="white", linewidth=0.7),
    geom_path(data=right_arc, aes(x=x, y=y), inherit.aes=FALSE, color="white", linewidth=0.7),
    annotate("segment", x=0,         xend=-2,           y=goal_ymin, yend=goal_ymin, color="white", linewidth=1),
    annotate("segment", x=0,         xend=-2,           y=goal_ymax, yend=goal_ymax, color="white", linewidth=1),
    annotate("segment", x=pitch_len, xend=pitch_len+2,  y=goal_ymin, yend=goal_ymin, color="white", linewidth=1),
    annotate("segment", x=pitch_len, xend=pitch_len+2,  y=goal_ymax, yend=goal_ymax, color="white", linewidth=1),
    annotate("path", x=corner_r*cos(seq(0, pi/2, length.out=80)),
             y=corner_r*sin(seq(0, pi/2, length.out=80)), color="white", linewidth=0.7),
    annotate("path", x=corner_r*cos(seq(pi/2, pi, length.out=80)),
             y=pitch_wid + corner_r*sin(seq(pi/2, pi, length.out=80)), color="white", linewidth=0.7),
    annotate("path", x=pitch_len + corner_r*cos(seq(pi, 3*pi/2, length.out=80)),
             y=pitch_wid + corner_r*sin(seq(pi, 3*pi/2, length.out=80)), color="white", linewidth=0.7),
    annotate("path", x=pitch_len + corner_r*cos(seq(3*pi/2, 2*pi, length.out=80)),
             y=corner_r*sin(seq(3*pi/2, 2*pi, length.out=80)), color="white", linewidth=0.7)
  )
}

complete_zone_grid <- function(dt, value_col, nx, ny, pitch_len, pitch_wid) {
  grid <- data.table(zone = as.character(seq_len(nx * ny)))
  if (!(value_col %in% names(dt))) stop("complete_zone_grid: missing column ", value_col)
  if (!("zone" %in% names(dt)))    stop("complete_zone_grid: missing column zone")
  dt2 <- dt[, .(zone = as.character(zone), val = get(value_col))]
  setnames(dt2, "val", value_col)
  out <- merge(grid, dt2, by = "zone", all.x = TRUE)
  out[is.na(get(value_col)), (value_col) := 0]
  out[, zone_i := as.integer(zone)]
  out[, x := ((zone_i - 1L) %% nx + 0.5) * (pitch_len / nx)]
  out[, y := pitch_wid - (((zone_i - 1L) %/% nx + 0.5) * (pitch_wid / ny))]
  out
}

.show_flags <- function(show) {
  allowed <- c("tiles","dot","arrow")
  if (missing(show) || is.null(show)) show <- allowed
  show <- unique(tolower(as.character(show)))
  bad  <- setdiff(show, allowed)
  if (length(bad) > 0)
    stop("Unknown show option(s): ", paste(bad, collapse=", "),
         ". Allowed: ", paste(allowed, collapse=", "))
  list(tiles = "tiles" %in% show, dot = "dot" %in% show, arrow = "arrow" %in% show)
}

plot_Da_pitch <- function(season_val, passer, prog_scale = 1.0,
                          show = c("tiles","dot","arrow")) {
  stopifnot(exists("player_season_avgpos"), exists("pass_given_vec"), exists("std_name"))
  sf          <- .show_flags(show)
  passer_std  <- std_name(passer)
  p           <- ggplot() + pitch_layers(PITCH_LEN, PITCH_WID)

  if (sf$tiles) {
    dtp <- copy(Da_plot_long)[season == season_val & passer_name == passer_std]
    if (nrow(dtp) == 0) stop("No Da rows for that (season, passer).")
    dtp <- complete_zone_grid(dtp, "D", nx, ny, PITCH_LEN, PITCH_WID)
    p <- p +
      geom_tile(data=dtp, aes(x=x, y=y, fill=D),
                width=PITCH_LEN/nx, height=PITCH_WID/ny, color="white", linewidth=0.15, alpha=0.70) +
      scale_fill_gradient(low="#FFF5F5", high="#FF0000", trans=scales::log1p_trans()) +
      labs(fill="Share")
  }

  pos <- NULL
  if (sfdot||sfarrow) {
    pos <- player_season_avgpos[season == season_val & player_name == passer_std,
                                .(x0 = avg_action_x, y0_raw = avg_action_y)][1]
    if (nrow(pos) == 0 || !is.finite(posx0)||!is.finite(posy0_raw))
      stop("No avg_action position found for this (season, player).")
    pos[, y0 := PITCH_WID - y0_raw]
  }

  if (sf$arrow) {
    prog <- suppressWarnings(as.numeric(
      pass_given_vec[season == season_val & player_name == passer_std, pass_given_prog][1]
    ))
    clamp <- function(v, lo, hi) pmin(pmax(v, lo), hi)
    seg   <- data.table(x=posx0,y=posy0,
                        xend=clamp(posx0+progscale*prog,0,PITCHLEN),yend=posy0)
    arrow_spec <- grid::arrow(length=grid::unit(0.07,"inches"), angle=12, type="open")
    if (is.finite(prog)) {
      p <- p +
        geom_segment(data=seg, aes(x=x, y=y, xend=xend, yend=yend),
                     inherit.aes=FALSE, color="white", linewidth=2, arrow=arrow_spec) +
        geom_segment(data=seg, aes(x=x, y=y, xend=xend, yend=yend),
                     inherit.aes=FALSE, color="#FF0000", linewidth=0.8, arrow=arrow_spec)
    }
  }

  if (sf$dot)
    p <- p + geom_point(data=pos, aes(x=x0, y=y0), inherit.aes=FALSE,
                        shape=21, size=4.2, stroke=1.2, fill="#FF0000", color="white")

  subtitle_parts <- c()
  if (sf$tiles) subtitle_parts <- c(subtitle_parts, "Squares = Da distribution")
  if (sf$dot)   subtitle_parts <- c(subtitle_parts, "Dot = avg action position")
  if (sf$arrow) subtitle_parts <- c(subtitle_parts, paste0("Arrow = avg pass progress (scale=", prog_scale, ")"))

  p + coord_fixed(xlim=c(0,PITCH_LEN), ylim=c(0,PITCH_WID), expand=FALSE) +
    theme_void() +
    labs(title    = paste0("Da — ", passer, " (", season_val, ")"),
         subtitle = paste(subtitle_parts, collapse=" | "))
}

plot_Rv_pitch <- function(season_val, receiver, prog_scale = 1.0, head_gap_m = 3,
                          show = c("tiles","dot","arrow")) {
  stopifnot(exists("player_season_avgpos"), exists("pass_received_vec"), exists("std_name"))
  sf            <- .show_flags(show)
  receiver_std  <- std_name(receiver)
  p             <- ggplot() + pitch_layers(PITCH_LEN, PITCH_WID)

  if (sf$tiles) {
    dtp <- copy(Rv_plot_long)[season == season_val & receiver_name == receiver_std]
    if (nrow(dtp) == 0) stop("No Rv rows for that (season, receiver).")
    dtp <- complete_zone_grid(dtp, "Rv", nx, ny, PITCH_LEN, PITCH_WID)
    p <- p +
      geom_tile(data=dtp, aes(x=x, y=y, fill=Rv),
                width=PITCH_LEN/nx, height=PITCH_WID/ny, color="white", linewidth=0.15, alpha=0.70) +
      scale_fill_gradient(low="#F5F7FF", high="#0000FF", trans=scales::log1p_trans()) +
      labs(fill="Share")
  }

  pos <- NULL
  if (sfdot||sfarrow) {
    pos <- player_season_avgpos[season == season_val & player_name == receiver_std,
                                .(x0 = avg_action_x, y0_raw = avg_action_y)][1]
    if (nrow(pos) == 0 || !is.finite(posx0)||!is.finite(posy0_raw))
      stop("No avg_action position found for this (season, player).")
    pos[, y0 := PITCH_WID - y0_raw]
  }

  if (sf$arrow) {
    prog <- suppressWarnings(as.numeric(
      pass_received_vec[season == season_val & player_name == receiver_std, pass_recv_prog_w][1]
    ))
    clamp <- function(v, lo, hi) pmin(pmax(v, lo), hi)
    gap   <- if (sf$dot) head_gap_m else 0
    seg   <- NULL
    if (is.finite(prog) && prog != 0) {
      dir  <- ifelse(prog > 0, 1, -1)
      xend <- clamp(pos$x0 - dir * gap, 0, PITCH_LEN)
      x    <- clamp(xend - prog_scale * prog, 0, PITCH_LEN)
      seg  <- data.table(x=x, y=posy0,xend=xend,yend=posy0)
    }
    arrow_spec <- grid::arrow(length=grid::unit(0.07,"inches"), angle=12, type="open")
    if (!is.null(seg)) {
      p <- p +
        geom_segment(data=seg, aes(x=x, y=y, xend=xend, yend=yend),
                     inherit.aes=FALSE, color="white", linewidth=2, arrow=arrow_spec) +
        geom_segment(data=seg, aes(x=x, y=y, xend=xend, yend=yend),
                     inherit.aes=FALSE, color="#0000FF", linewidth=0.8, arrow=arrow_spec)
    }
  }

  if (sf$dot)
    p <- p + geom_point(data=pos, aes(x=x0, y=y0), inherit.aes=FALSE,
                        shape=21, size=4.2, stroke=1.2, fill="#0000FF", color="white")

  subtitle_parts <- c()
  if (sf$tiles) subtitle_parts <- c(subtitle_parts, "Squares = Rv distribution")
  if (sf$dot)   subtitle_parts <- c(subtitle_parts, "Dot = avg action position")
  if (sf$arrow) {
    gap_txt        <- if (sf$dot) paste0(", gap=", head_gap_m, "m") else ""
    subtitle_parts <- c(subtitle_parts,
                        paste0("Arrow = avg received-pass progress (scale=", prog_scale, gap_txt, ")"))
  }

  p + coord_fixed(xlim=c(0,PITCH_LEN), ylim=c(0,PITCH_WID), expand=FALSE) +
    theme_void() +
    labs(title    = paste0("Rv — ", receiver, " (", season_val, ")"),
         subtitle = paste(subtitle_parts, collapse=" | "))
}

###############################################################################
# MODELLING: new-pairs dataset, 85/15 pair-level split, 2-step model
###############################################################################

# ============================================================
# 20) BUILD MODEL DATASET (new pairs only, all features finite)
# ============================================================
dt_model <- as.data.table(copy(final_pairs_prevseason_filtered))
dt_model <- dt_model[
  minutes_together  >= MIN_MINUTES  &
    both_in_db_prev_season == TRUE  &
    is_new_pair_season     == TRUE  &
    is.finite(joi_per90)            &
    is.finite(compat_sum_prev)      &
    is.finite(vaep_per90_prev_p1)   &
    is.finite(vaep_per90_prev_p2)   &
    is.finite(position_distance_prev) &
    is.finite(role_match_sum_prev)
]

cat("\n--- DATASET FOR MODEL (NEW PAIRS ONLY) ---\n")
cat("Rows:",         nrow(dt_model), "\n")
cat("Unique pairs:", uniqueN(dt_model$pair_id), "\n")
if (nrow(dt_model) == 0)
  stop("dt_model is empty after filtering. Check joins for VAEP/90 and position_distance_prev.")

# ============================================================
# 21) MARKET VALUES FROM TRANSFERMARKT
# ============================================================
needed_season_prevs <- sort(unique(na.omit(dt_model$season_prev)))
needed_start_years  <- suppressWarnings(as.integer(substr(needed_season_prevs, 1, 2))) + 2000L
needed_start_years  <- needed_start_years[!is.na(needed_start_years)]
cat("\n--- MARKET VALUES: need start years:", paste(needed_start_years, collapse = ", "), "---\n")

LEAGUE_TM_CFG <- list(
  EPL = list(slug = "premier-league", tm_code = "GB1"),
  GB  = list(slug = "bundesliga",     tm_code = "L1"),
  SLL = list(slug = "laliga",         tm_code = "ES1"),
  ISA = list(slug = "serie-a",        tm_code = "IT1"),
  FL1 = list(slug = "ligue-1",        tm_code = "FR1"),
  SSD = list(slug = "laliga2",        tm_code = "ES2")
)

new_rows <- list()

for (lc in names(LEAGUE_TM_CFG)) {
  lg <- LEAGUE_TM_CFG[[lc]]

  for (yr in needed_start_years) {
    season_key <- sprintf("%02d-%02d", yr %% 100L, (yr + 1L) %% 100L)

    cat(sprintf("  [%s] %s: fetching team URLs ...\n", lc, season_key))
    team_urls <- get_team_urls_tm(lgslug,lgtm_code, yr)
    Sys.sleep(4)

    if (length(team_urls) == 0) {
      cat("  no team URLs returned\n"); next
    }

    for (tu in team_urls) {
      team_label <- sub(paste0(".*", TM_BASE, "/([^/]+)/startseite.*"), "\\1", tu)
      cat(sprintf("    %s [%s %s] ...", team_label, lc, season_key))
      df_team <- parse_team_page_tm(tu)
      if (!is.null(df_team) && nrow(df_team) > 0) {
        out_team <- data.table(
          player_name_raw = df_team$player_name,
          mv_eur          = df_team$mv_eur,
          league_code     = lc,
          season          = season_key,
          team_raw        = team_label
        )
        new_rows[[paste0(lc, "_", yr, "_", team_label)]] <- out_team
        cat("", nrow(out_team), "rows\n")
      } else {
        cat(" no data\n")
      }
      Sys.sleep(3)
    }
  }
}

mv_scraped <- rbindlist(new_rows, fill = TRUE)

if (nrow(mv_scraped) > 0) {
  mv_scraped[, player_name_std := std_name(player_name_raw)]
  mv_scraped[, mv_eur_mil      := mv_eur / 1e6]
  mv_lookup <- mv_scraped[
    !is.na(player_name_std) & is.finite(mv_eur_mil),
    .(mv_eur_mil = max(mv_eur_mil, na.rm = TRUE)),
    by = .(season, player_name_std)
  ]
  setkey(mv_lookup, season, player_name_std)
} else {
  mv_lookup <- data.table(season = character(), player_name_std = character(), mv_eur_mil = numeric())
  cat("WARNING: no market values scraped. All MV features will be NA.\n")
}

dt_model[, season_prev  := as.character(season_prev)]
dt_model[, player1_name := std_name(player1_name)]
dt_model[, player2_name := std_name(player2_name)]

p1_mv <- copy(mv_lookup)
setnames(p1_mv, c("season","player_name_std","mv_eur_mil"),
                c("season_prev","player1_name","mv_usd_mil_prev_p1"))
p2_mv <- copy(mv_lookup)
setnames(p2_mv, c("season","player_name_std","mv_eur_mil"),
                c("season_prev","player2_name","mv_usd_mil_prev_p2"))
setkey(p1_mv, season_prev, player1_name)
setkey(p2_mv, season_prev, player2_name)

dt_model[p1_mv, mv_usd_mil_prev_p1 := i.mv_usd_mil_prev_p1, on = .(season_prev, player1_name)]
dt_model[p2_mv, mv_usd_mil_prev_p2 := i.mv_usd_mil_prev_p2, on = .(season_prev, player2_name)]

# Manually filled values for players not found on Transfermarkt
missing_p1 <- dt_model[is.na(mv_usd_mil_prev_p1),
                        unique(data.table(season_prev, player_name = player1_name))]
missing_p2 <- dt_model[is.na(mv_usd_mil_prev_p2),
                        unique(data.table(season_prev, player_name = player2_name))]
missing_mv <- unique(rbind(missing_p1, missing_p2))

if (nrow(missing_mv) > 0 && file.exists(mv_manual_fill_path)) {
  manual_filled <- as.data.table(read_xlsx(mv_manual_fill_path))
  manual_filled[, mv_eur_mil := suppressWarnings(
    as.numeric(gsub(",", ".", as.character(mv_eur_mil)))
  )]
  manual_filled <- manual_filled[is.finite(mv_eur_mil)]
  manual_filled[, season_prev     := as.character(season_prev)]
  manual_filled[, player_name_std := std_name(player_name)]

  if (nrow(manual_filled) > 0) {
    mm1 <- manual_filled[, .(season_prev, player1_name = player_name_std,
                              mv_usd_mil_prev_p1 = mv_eur_mil)]
    mm2 <- manual_filled[, .(season_prev, player2_name = player_name_std,
                              mv_usd_mil_prev_p2 = mv_eur_mil)]
    dt_model[mm1, mv_usd_mil_prev_p1 := fifelse(is.na(mv_usd_mil_prev_p1),
                                                 i.mv_usd_mil_prev_p1, mv_usd_mil_prev_p1),
             on = .(season_prev, player1_name)]
    dt_model[mm2, mv_usd_mil_prev_p2 := fifelse(is.na(mv_usd_mil_prev_p2),
                                                 i.mv_usd_mil_prev_p2, mv_usd_mil_prev_p2),
             on = .(season_prev, player2_name)]
    cat(sprintf("Applied %d manually filled market values from Excel.\n", nrow(manual_filled)))
  }

  missing_p1 <- dt_model[is.na(mv_usd_mil_prev_p1),
                          unique(data.table(season_prev, player_name = player1_name))]
  missing_p2 <- dt_model[is.na(mv_usd_mil_prev_p2),
                          unique(data.table(season_prev, player_name = player2_name))]
  missing_mv <- unique(rbind(missing_p1, missing_p2))
}

if (nrow(missing_mv) > 0) {
  if (nrow(missing_mv) > 20) {
    missing_mv[, mv_eur_mil := NA_real_]
    writexl::write_xlsx(as.data.frame(missing_mv), mv_manual_fill_path)
    stop(sprintf(
      paste0("%d player-seasons still missing market values.\n",
             "An Excel file has been written to:\n  %s\n",
             "Fill the 'mv_eur_mil' column (EUR millions, e.g. 25.5) and re-run the script."),
      nrow(missing_mv), mv_manual_fill_path
    ))
  }
  cat(sprintf(
    "  %d player-season(s) still missing MV after all sources — filtering those pairs out.\n",
    nrow(missing_mv)
  ))
  print(missing_mv[, .(season_prev, player_name)])
  dt_model <- dt_model[!is.na(mv_usd_mil_prev_p1) & !is.na(mv_usd_mil_prev_p2)]
}

dt_model[, mv_usd_mil_sum_prev     := mv_usd_mil_prev_p1 + mv_usd_mil_prev_p2]
dt_model[, mv_usd_mil_absdiff_prev := abs(mv_usd_mil_prev_p1 - mv_usd_mil_prev_p2)]

cat("\n--- MARKET VALUE DIAGNOSTICS ---\n")
cat("Missing p1 mv:", dt_model[is.na(mv_usd_mil_prev_p1), .N], "\n")
cat("Missing p2 mv:", dt_model[is.na(mv_usd_mil_prev_p2), .N], "\n")

# ============================================================
# 22) PLAYING STYLE SIMILARITY (PRIOR SEASON)
# ============================================================
p1_style <- copy(player_season_style)
setnames(p1_style,
  c("season","player_name", paste0(off_sub_cols)),
  c("season_prev","player1_name", paste0(off_sub_cols, "_p1")))
setkey(p1_style, season_prev, player1_name)

p2_style <- copy(player_season_style)
setnames(p2_style,
  c("season","player_name", paste0(off_sub_cols)),
  c("season_prev","player2_name", paste0(off_sub_cols, "_p2")))
setkey(p2_style, season_prev, player2_name)

p1_style_cols <- paste0(off_sub_cols, "_p1")
p2_style_cols <- paste0(off_sub_cols, "_p2")

dt_model[p1_style, (p1_style_cols) := mget(paste0("i.", p1_style_cols)),
         on = .(season_prev, player1_name)]
dt_model[p2_style, (p2_style_cols) := mget(paste0("i.", p2_style_cols)),
         on = .(season_prev, player2_name)]

# 4-dimensional Euclidean distance in offensive style subspace
dt_model[, style_dist_prev := sqrt(
  (off_salida_p1 - off_salida_p2)^2 +
    (off_canal_p1  - off_canal_p2)^2  +
    (off_pos_p1    - off_pos_p2)^2    +
    (off_poses_p1  - off_poses_p2)^2
)]

cat("\n--- STYLE DISTANCE DIAGNOSTICS (4D offensive subspace) ---\n")
for (cc in c(p1_style_cols, p2_style_cols))
  cat("Missing", cc, ":", dt_model[is.na(get(cc)), .N], "\n")
cat("Missing style_dist_prev: ", dt_model[is.na(style_dist_prev), .N], "\n")
print(summary(dt_model$style_dist_prev))

dt_model <- dt_model[is.finite(style_dist_prev)]
cat("Rows in dt_model after style filter:", nrow(dt_model), "\n")

dt_model[, mv_disp_ratio_prev := fifelse(
  is.finite(mv_usd_mil_sum_prev) & mv_usd_mil_sum_prev > 0,
  mv_usd_mil_absdiff_prev / mv_usd_mil_sum_prev,
  NA_real_
)]

cat("Missing action_emd_prev in dt_model:", dt_model[is.na(action_emd_prev), .N], "\n")

# ============================================================
# 23) PASS COMPLEMENTARITY METRICS
# ============================================================

# --- 23.1) Pass vector Euclidean distance (a gives, b receives) ---
dt_model[, pass_vec_dist_a_to_b :=
           sqrt((pass_given_dx_prev_p1 - pass_recv_dx_w_prev_p2)^2 +
                  (pass_given_dy_prev_p1 - pass_recv_dy_w_prev_p2)^2)]
dt_model[, pass_vec_dist_b_to_a :=
           sqrt((pass_given_dx_prev_p2 - pass_recv_dx_w_prev_p1)^2 +
                  (pass_given_dy_prev_p2 - pass_recv_dy_w_prev_p1)^2)]
dt_model[, pass_vec_dist_sum    := pass_vec_dist_a_to_b + pass_vec_dist_b_to_a]
dt_model[, pass_vec_comp_a_to_b := 1 / (1 + pass_vec_dist_a_to_b)]
dt_model[, pass_vec_comp_b_to_a := 1 / (1 + pass_vec_dist_b_to_a)]
dt_model[, pass_vec_comp_sum    := pass_vec_comp_a_to_b + pass_vec_comp_b_to_a]

cat("\n--- PASS VECTOR EUCLIDEAN METRIC DIAGNOSTICS ---\n")
cat("Missing a->b dist:", sum(is.na(dt_model$pass_vec_dist_a_to_b)), "\n")
cat("Missing b->a dist:", sum(is.na(dt_model$pass_vec_dist_b_to_a)), "\n")

# --- 23.2) Pass progressiveness complementarity (normalised abs diff) ---
dt_model[, pass_prog_dist_a_to_b :=
           abs(pass_given_prog_prev_p1 - pass_recv_prog_w_prev_p2) /
           (abs(pass_given_prog_prev_p1) + abs(pass_recv_prog_w_prev_p2))]
dt_model[, pass_prog_dist_b_to_a :=
           abs(pass_given_prog_prev_p2 - pass_recv_prog_w_prev_p1) /
           (abs(pass_given_prog_prev_p2) + abs(pass_recv_prog_w_prev_p1))]
dt_model[, pass_prog_dist_sum    := pass_prog_dist_a_to_b + pass_prog_dist_b_to_a]
dt_model[, pass_prog_comp_a_to_b := 1 / (1 + pass_prog_dist_a_to_b)]
dt_model[, pass_prog_comp_b_to_a := 1 / (1 + pass_prog_dist_b_to_a)]
dt_model[, pass_prog_comp_sum    := pass_prog_comp_a_to_b + pass_prog_comp_b_to_a]

cat("\n--- PASS PROGRESS COMPLEMENTARITY DIAGNOSTICS ---\n")
cat("Missing a->b:", sum(is.na(dt_model$pass_prog_dist_a_to_b)), "\n")
cat("Missing b->a:", sum(is.na(dt_model$pass_prog_dist_b_to_a)), "\n")

# --- 23.3) Pass absolute width complementarity (normalised abs diff) ---
dt_model[, pass_abswidth_dist_a_to_b :=
           abs(pass_given_width_abs_prev_p1 - pass_recv_width_abs_w_prev_p2) /
           (abs(pass_given_width_abs_prev_p1) + abs(pass_recv_width_abs_w_prev_p2))]
dt_model[, pass_abswidth_dist_b_to_a :=
           abs(pass_given_width_abs_prev_p2 - pass_recv_width_abs_w_prev_p1) /
           (abs(pass_given_width_abs_prev_p2) + abs(pass_recv_width_abs_w_prev_p1))]
dt_model[, pass_abswidth_dist_sum    := pass_abswidth_dist_a_to_b + pass_abswidth_dist_b_to_a]
dt_model[, pass_abswidth_comp_a_to_b := 1 / (1 + pass_abswidth_dist_a_to_b)]
dt_model[, pass_abswidth_comp_b_to_a := 1 / (1 + pass_abswidth_dist_b_to_a)]
dt_model[, pass_abswidth_comp_sum    := pass_abswidth_comp_a_to_b + pass_abswidth_comp_b_to_a]

cat("\n--- PASS ABS-WIDTH COMPLEMENTARITY DIAGNOSTICS ---\n")
cat("Missing a->b:", sum(is.na(dt_model$pass_abswidth_dist_a_to_b)), "\n")
cat("Missing b->a:", sum(is.na(dt_model$pass_abswidth_dist_b_to_a)), "\n")

# ============================================================
# 24) TRAIN / TEST SPLIT (pair-level, no leakage)
# ============================================================
dt_model <- dt_model[minutes_together > MODEL_MIN_MINUTES]
cat(sprintf("\n--- dt_model filtered to >%d min together: %d rows, %d pairs ---\n",
            MODEL_MIN_MINUTES, nrow(dt_model), uniqueN(dt_model$pair_id)))
if (nrow(dt_model) == 0) stop("No pairs remain after minutes filter.")

rmse <- function(y, yhat) sqrt(mean((y - yhat)^2, na.rm = TRUE))

set.seed(SEED)
pair_ids  <- unique(dt_model$pair_id)
train_ids <- sample(pair_ids, size = floor(0.85 * length(pair_ids)), replace = FALSE)
test_ids  <- setdiff(pair_ids, train_ids)

dt_train <- dt_model[pair_id %in% train_ids]
dt_test  <- dt_model[pair_id %in% test_ids]
stopifnot(length(intersect(unique(dt_trainpairid),unique(dttestpair_id))) == 0)

cat("\n--- 85/15 SPLIT (PAIR-LEVEL) ---\n")
cat("Train rows:", nrow(dt_train), " | Train pairs:", uniqueN(dt_train$pair_id), "\n")
cat("Test  rows:", nrow(dt_test),  " | Test  pairs:", uniqueN(dt_test$pair_id),  "\n")

# ============================================================
# 25) TWO-STEP MODEL
# ============================================================
baseline_mean  <- mean(dt_train$joi_per90, na.rm = TRUE)
rmse_baseline  <- rmse(dt_test$joi_per90, rep(baseline_mean, nrow(dt_test)))

# Step 1: JOI ~ market value sum + relative disparity
m1 <- lm(joi_per90 ~ mv_usd_mil_sum_prev + I(mv_usd_mil_absdiff_prev / mv_usd_mil_sum_prev),
         data = dt_train)
dt_train[, resid1 := joi_per90 - predict(m1, newdata = dt_train)]

# Step 2: residuals ~ compatibility features
m2 <- lm(resid1 ~ compat_sum_prev + action_emd_prev + pass_prog_dist_sum +
            role_match_sum_prev + style_dist_prev,
         data = dt_train)

pred_test      <- predict(m1, newdata = dt_test) + predict(m2, newdata = dt_test)
rmse_two_step  <- rmse(dt_test$joi_per90, pred_test)
pct_improve    <- 100 * (rmse_baseline - rmse_two_step) / rmse_baseline

cat("\n--- RESULTS (TEST SET) ---\n")
cat("Baseline RMSE:      ", rmse_baseline,  "\n")
cat("Two-step RMSE:      ", rmse_two_step,  "\n")
cat("Percent improvement:", pct_improve,    "%\n")

cat("\n--- STEP 1 SUMMARY ---\n")
print(summary(m1))

cat("\n--- STEP 2 SUMMARY ---\n")
print(summary(m2))

# ============================================================
# 25a) INFORMED BENCHMARK
#      Mean JOI/90 of each player's qualifying pairings in strictly
#      earlier seasons; pair prediction is the mean of the two.
# ============================================================
jr <- rbindlist(lapply(Sys.glob(file.path(vaep_dir, "joi_pairs_*.csv")), fread,
        select = c("season","player1_name","player2_name","minutes_together","joi_per90"),
        showProgress = FALSE), fill = TRUE)
jr[, `:=`(q1 = std_name(player1_name), q2 = std_name(player2_name))]
jr <- jr[!is.na(q1) & !is.na(q2) & is.finite(joi_per90) & is.finite(minutes_together) &
           minutes_together > MODEL_MIN_MINUTES]
jr[, sy := as.integer(substr(norm_season(season), 1, 2))]
# 21-22 is the VAEP training season and has no JOI
jr <- jr[is.finite(sy) & sy >= 22]
jl <- rbindlist(list(jr[, .(player = q1, sy, joi_per90)],
                     jr[, .(player = q2, sy, joi_per90)]))
jp <- jl[, .(s = sum(joi_per90), n = .N), by = .(player, sy)]
setorder(jp, player, sy)
jp[, `:=`(cs = cumsum(s) - s, cn = cumsum(n) - n), by = player]
informed_hist <- jp[, .(player, sy,
                        prior_mean = fifelse(cn > 0, cs / cn, NA_real_), prior_n = cn)]
setkey(informed_hist, player, sy)

dt_bench <- copy(dt_test)
dt_bench[, sy := as.integer(substr(season, 1, 2))]
dt_bench[informed_hist, inf_a := i.prior_mean, on = c(player1_name = "player", sy = "sy")]
dt_bench[informed_hist, inf_b := i.prior_mean, on = c(player2_name = "player", sy = "sy")]
dt_bench[, pred_informed := fifelse(
  is.finite(inf_a) & is.finite(inf_b), (inf_a + inf_b) / 2,
  fifelse(is.finite(inf_a), inf_a, fifelse(is.finite(inf_b), inf_b, baseline_mean)))]

pred_test_mv    <- predict(m1, newdata = dt_test)
pred_test_model <- pred_test_mv + predict(m2, newdata = dt_test)
rmse_naive    <- rmse_baseline
rmse_informed <- rmse(dt_benchjoiper90,dtbenchpred_informed)
rmse_mv_only  <- rmse(dt_test$joi_per90,  pred_test_mv)
rmse_model    <- rmse(dt_test$joi_per90,  pred_test_model)
oos_r2 <- function(yy, pp) 1 - sum((yy - pp)^2, na.rm = TRUE) /
                               sum((yy - mean(yy, na.rm = TRUE))^2, na.rm = TRUE)
pct <- function(from, to) 100 * (from - to) / from

cat("\n============================================================\n")
cat("BENCHMARK COMPARISON - TEST SET (", nrow(dt_test), " rows )\n", sep = "")
cat("============================================================\n")
cat(sprintf("Informed coverage: both %d | one %d | neither %d\n",
            dt_bench[is.finite(inf_a) & is.finite(inf_b), .N],
            dt_bench[xor(is.finite(inf_a), is.finite(inf_b)), .N],
            dt_bench[!is.finite(inf_a) & !is.finite(inf_b), .N]))
cat("\n")
cat(sprintf("  %-32s %.6f\n", "naive baseline (train mean)", rmse_naive))
cat(sprintf("  %-32s %.6f\n", "informed benchmark",          rmse_informed))
cat(sprintf("  %-32s %.6f\n", "market-value-only model",     rmse_mv_only))
cat(sprintf("  %-32s %.6f\n", "complete model",              rmse_model))
cat("\n")
cat(sprintf("  informed vs naive          : %+6.2f%%\n", pct(rmse_naive, rmse_informed)))
cat(sprintf("  market-value-only vs naive : %+6.2f%%   vs informed: %+6.2f%%\n",
            pct(rmse_naive, rmse_mv_only), pct(rmse_informed, rmse_mv_only)))
cat(sprintf("  complete model    vs naive : %+6.2f%%   vs informed: %+6.2f%%\n",
            pct(rmse_naive, rmse_model),   pct(rmse_informed, rmse_model)))
cat(sprintf("  test R2, complete model    : %.4f   (market-value only %.4f)\n",
            oos_r2(dt_test$joi_per90, pred_test_model),
            oos_r2(dt_test$joi_per90, pred_test_mv)))
cat(sprintf("  Spearman rho (pred vs real): %.4f\n",
            cor(pred_test_model, dt_test$joi_per90, method = "spearman")))
cat("============================================================\n")

# ============================================================
# 25b) PER-PAIR PREDICTION DECOMPOSITION
# ============================================================
dt_decomp <- copy(dt_model)

dt_decomp[, pred_step1  := predict(m1, newdata = dt_decomp)]
dt_decomp[, pred_step2  := predict(m2, newdata = dt_decomp)]
dt_decomp[, pred_joi    := pred_step1 + pred_step2]
dt_decomp[, residual    := joi_per90  - pred_joi]

# Signed contribution = coefficient × feature value
coef_m1 <- coef(m1)
coef_m2 <- coef(m2)

dt_decomp[, contrib_intercept := coef_m1["(Intercept)"] + coef_m2["(Intercept)"]]
dt_decomp[, contrib_mv_sum    := coef_m1["mv_usd_mil_sum_prev"] * mv_usd_mil_sum_prev]
dt_decomp[, contrib_mv_disp   := coef_m1["I(mv_usd_mil_absdiff_prev/mv_usd_mil_sum_prev)"] *
                                   (mv_usd_mil_absdiff_prev / mv_usd_mil_sum_prev)]
dt_decomp[, contrib_compat    := coef_m2["compat_sum_prev"]     * compat_sum_prev]
dt_decomp[, contrib_emd       := coef_m2["action_emd_prev"]     * action_emd_prev]
dt_decomp[, contrib_prog      := coef_m2["pass_prog_dist_sum"]  * pass_prog_dist_sum]
dt_decomp[, contrib_role      := coef_m2["role_match_sum_prev"] * role_match_sum_prev]
dt_decomp[, contrib_style     := coef_m2["style_dist_prev"]     * style_dist_prev]

dt_decomp[, split := fifelse(pair_id %in% train_ids, "train", "test")]

out_decomp <- dt_decomp[, .(
  season, player1_name, player2_name, split,
  joi_per90, pred_joi, residual,
  contrib_intercept, contrib_mv_sum, contrib_mv_disp,
  contrib_compat, contrib_emd, contrib_prog, contrib_role, contrib_style,
  mv_usd_mil_sum_prev, mv_disp_ratio_prev,
  compat_sum_prev, action_emd_prev, pass_prog_dist_sum,
  role_match_sum_prev, style_dist_prev
)]
out_decomp[, abs_residual := abs(residual)]
setorder(out_decomp, split, -abs_residual)
out_decomp[, abs_residual := NULL]

fwrite(out_decomp, decomp_path)
cat("\nPer-pair prediction decomposition saved to:\n  ", decomp_path, "\n")
cat("Rows:", nrow(out_decomp), " | Test rows:", out_decomp[split == "test", .N], "\n")
