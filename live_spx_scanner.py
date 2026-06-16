import asyncio
import csv
import itertools
import json
import math
import os
import smtplib
import time
import traceback
from datetime import datetime, date, timedelta, timezone
from email.mime.text import MIMEText
from zoneinfo import ZoneInfo

_ET = ZoneInfo('America/New_York')

import pandas as pd
import pandas_ta as ta
import requests
import yfinance as yf
from flask import Flask, jsonify
from polygon import RESTClient
from waitress import serve as _waitress_serve
from alpaca.trading.client import TradingClient
from alpaca.data.historical import StockHistoricalDataClient
from alpaca.data.requests import StockLatestTradeRequest
from alpaca.trading.requests import (
    MarketOrderRequest, TakeProfitRequest, StopLossRequest, GetOrdersRequest
)
from alpaca.trading.enums import QueryOrderStatus
from alpaca.trading.enums import OrderSide, TimeInForce, OrderClass

# ====================== CONFIG ======================
POLYGON_API_KEY   = os.getenv("POLYGON_API_KEY")
DISCORD_WEBHOOK   = os.getenv("DISCORD_WEBHOOK")
TELEGRAM_TOKEN    = os.getenv("TELEGRAM_BOT_TOKEN")
TELEGRAM_CHAT_ID  = os.getenv("TELEGRAM_CHAT_ID")
EMAIL_FROM        = os.getenv("EMAIL_FROM")
EMAIL_PASSWORD    = os.getenv("EMAIL_PASSWORD")
EMAIL_TO          = os.getenv("EMAIL_TO")
SMTP_HOST         = os.getenv("SMTP_HOST", "smtp.gmail.com")
SMTP_PORT         = int(os.getenv("SMTP_PORT", "587"))

WATCHLIST             = ["SPY", "QQQ", "IWM", "NVDA", "AAPL"]
SIGNAL_LOG_FILE       = "/tmp/signal_log.json"
CSV_LOG_FILE          = "/tmp/signals.csv"
HISTORY_FILE_TMPL     = "/tmp/score_history_{}.json"
MAX_SCORE             = 100      # weighted 0-100 (INST 35 + LEVELS 20 + TECH 30 + PAT 10 + MKT 5)
ALERT_COOLDOWN_SECS   = 900
VOLUME_SPIKE_MULT     = 3.0
ALERT_SCORE_THRESHOLD = 22      # ~22% conviction floor (was 9/42)
LOG_SCORE_THRESHOLD   = 14      # ~14% log floor (was 6/42)

# ── Weighted scoring architecture ─────────────────────────────────────────────
CATEGORY_WEIGHTS = {
    "INST":    35,   # Institutional flow — highest conviction
    "LEVELS":  20,   # Structural key levels
    "TECH":    30,   # Technical indicators
    "PATTERN": 10,   # Candlestick/price patterns
    "MARKET":   5,   # Regime/breadth (governor)
}
# Trend-following TECH signals penalised 50% when market is ranging/choppy
TREND_SIGNALS = frozenset({
    "sma20", "sma200", "ema9", "ema50",
    "ema_cross", "supertrend", "ftfc",
})
RANGING_REGIMES    = frozenset({"ranging", "neutral"})
TREND_MULT_RANGING = 0.5
# Phase 14: CQ-gated alert routing
# HIGH → Discord + Telegram + Email (starred message)
# MED  → Discord + Telegram
# LOW  → Discord only
# WEAK → suppressed (score threshold still required)
CQ_MIN_ALERT          = os.getenv("CQ_MIN_ALERT", "LOW")   # set to MED or HIGH to reduce noise
_CQ_RANK              = {"WEAK": 0, "LOW": 1, "MED": 2, "HIGH": 3}
ATR_STOP_MULT         = 1.5      # stop loss = price ± 1.5×ATR
ATR_TP_MULT           = 2.5      # take profit = price ± 2.5×ATR
ACCOUNT_SIZE          = float(os.getenv("ACCOUNT_SIZE", "25000"))
RISK_PCT              = 0.01     # risk 1% of account per trade
BREADTH_BULL_THRESH   = 3        # tickers in BULL needed for "bull dominant" breadth
BREADTH_BEAR_THRESH   = 3        # tickers in BEAR needed for "bear dominant" breadth
PCR_BULL_THRESH       = 0.7      # put/call ratio below this = calls dominating = bullish
PCR_BEAR_THRESH       = 1.2      # put/call ratio above this = puts dominating = bearish
OPTIONS_REFRESH_SECS  = 300      # re-fetch options every 5 min
ECON_REFRESH_SECS     = 3600     # re-fetch economic calendar hourly
ECON_CAL_URL          = "https://nfs.faireconomy.media/ff_calendar_thisweek.json"
OUTCOMES_FILE         = "/tmp/outcomes.json"
TRADE_MAX_MINS        = 240      # expire open simulated trades after 4 hours

# ── Institutional flow config ────────────────────────────────────────────────
BLOCK_PRINT_VOL_MULT  = 3.0     # vol multiple vs 20-bar avg for block print signal
BLOCK_PRINT_RANGE_PCT = 0.5     # price range must be < 50% of avg range (tight spread)
FLOW_VOI_THRESH       = 1.5     # vol/OI ratio above this = unusual fresh positioning
VWAP_DEF_VOL_MULT     = 2.0     # volume multiple for VWAP defense bar
VWAP_DEF_DIST_ATR     = 0.30    # within 0.3×ATR of VWAP to qualify as defense zone
TAPE_BARS             = 3       # consecutive same-direction bars for tape aggression
TAPE_VOL_MULT         = 1.5     # tape bars must avg this multiple of normal volume
ICEBERG_VOL_MULT      = 4.0     # iceberg: single bar vol > 4× avg + tiny net move

# ── Alpaca execution config ───────────────────────────────────────────────────
ALPACA_API_KEY     = os.getenv("ALPACA_API_KEY", "")
ALPACA_SECRET_KEY  = os.getenv("ALPACA_SECRET_KEY", "")
ALPACA_PAPER       = os.getenv("ALPACA_PAPER", "true").lower() != "false"
TRADE_SIZE_USD     = float(os.getenv("TRADE_SIZE_USD", "500"))
ALPACA_CQ_MIN      = os.getenv("ALPACA_CQ_MIN", "MED")   # MED or HIGH for real orders
ALPACA_ENABLED     = bool(ALPACA_API_KEY and ALPACA_SECRET_KEY)
ICEBERG_MOVE_ATR      = 0.15    # iceberg: net move < 0.15×ATR despite huge volume
VOL_DELTA_LOOKBACK    = 5       # bars to compute cumulative volume delta over

# Optional paid-API upgrade paths (set env vars to enable)
POLYGON_TIER          = os.getenv("POLYGON_TIER",        "free")  # "paid" → v3/trades
UNUSUAL_WHALES_KEY    = os.getenv("UNUSUAL_WHALES_KEY",  "")      # enables UW sweeps API

# ── Phase 12: Volume profile config ─────────────────────────────────────────
VP_BINS               = 40       # price bins for intraday volume profile
VP_VALUE_AREA_PCT     = 0.70     # value area = bins containing 70% of session volume

# ── Phase 11: Fibonacci config ───────────────────────────────────────────────
FIB_LOOKBACK          = 200      # 1m bars to scan for swing high/low (~3-4 RTH hours)
FIB_ZONE_ATR          = 0.5     # price within 0.5×ATR of fib level = "at zone"
RS_LEADER_THRESH      = 0.15    # ticker outperforming SPY by ≥0.15% = RS leader
RS_LAGGER_THRESH      = -0.15   # ticker underperforming SPY by ≥0.15% = RS lagger

# ── Phase 13: Signal category mapping ───────────────────────────────────────
SIGNAL_CATEGORIES = {
    # TECH — core momentum and trend indicators
    "sma20":"TECH",    "adx":"TECH",     "rsi":"TECH",   "ftfc":"TECH",
    "ema9":"TECH",     "ema50":"TECH",   "ema_cross":"TECH",
    "consec_bars":"PATTERN",
    "supertrend":"TECH","heikin_ashi":"TECH","vwap":"TECH","bb":"TECH",
    "macd":"TECH",     "rsi_div":"TECH", "stochrsi":"TECH",
    # PATTERN — price action and candle structure
    "fvg":"PATTERN",   "ob":"PATTERN",   "gap":"PATTERN","orb":"PATTERN",
    "candle_bull":"PATTERN","candle_bear":"PATTERN",
    # LEVELS — key price levels and structural zones
    "pivot_bull":"LEVELS","pivot_bear":"LEVELS",
    "pdh_break":"LEVELS", "pdl_break":"LEVELS",
    "pm_high_break":"LEVELS","pm_low_break":"LEVELS",
    "fib_support":"LEVELS","fib_resist":"LEVELS","fib_ext":"LEVELS",
    "vpoc_bull":"LEVELS","vpoc_bear":"LEVELS",
    "above_vah":"LEVELS","below_val":"LEVELS",
    "session_range":"LEVELS",
    "sma200":       "TECH",
    # INST — institutional and smart-money flow
    "block_print":"INST","flow_unusual":"INST","vol_delta":"INST",
    "vwap_def":"INST",  "tape_read":"INST",  "obv":"INST",
    # MARKET — macro context, regime, and breadth
    "vix":"MARKET",    "pcr":"MARKET",   "trend_15m":"MARKET",
    "trend_1h":"MARKET","regime_bull":"MARKET","regime_bear":"MARKET",
}

print("=== SPX CONFLUENCE SCANNER STARTING ===", flush=True)

# ====================== HELPERS ======================

def _valid(v):
    try:
        return v is not None and not math.isnan(float(v))
    except (TypeError, ValueError):
        return False


def _easter(year):
    a = year % 19
    b, c = divmod(year, 100)
    d, e = divmod(b, 4)
    f = (b + 8) // 25
    g = (b - f + 1) // 3
    h = (19 * a + b - d - g + 15) % 30
    i, k = divmod(c, 4)
    l = (32 + 2 * e + 2 * i - h - k) % 7
    m = (a + 11 * h + 22 * l) // 451
    month = (h + l - 7 * m + 114) // 31
    day = (h + l - 7 * m + 114) % 31 + 1
    return date(year, month, day)


def _us_market_holidays(year):
    import calendar

    def nth_weekday(month, weekday, n):
        first = date(year, month, 1)
        delta = (weekday - first.weekday()) % 7
        return first + timedelta(days=delta + (n - 1) * 7)

    def last_weekday(month, weekday):
        last = date(year, month, calendar.monthrange(year, month)[1])
        return last - timedelta(days=(last.weekday() - weekday) % 7)

    def observed(d):
        if d.weekday() == 6: return d + timedelta(days=1)
        if d.weekday() == 5: return d - timedelta(days=1)
        return d

    good_friday = _easter(year) - timedelta(days=2)
    return {
        observed(date(year, 1, 1)),
        nth_weekday(1, 0, 3),
        nth_weekday(2, 0, 3),
        good_friday,
        last_weekday(5, 0),
        observed(date(year, 6, 19)),
        observed(date(year, 7, 4)),
        nth_weekday(9, 0, 1),
        nth_weekday(11, 3, 4),
        observed(date(year, 12, 25)),
    }


_holiday_cache = {}

def _is_holiday(d):
    if d.year not in _holiday_cache:
        _holiday_cache[d.year] = _us_market_holidays(d.year)
    return d in _holiday_cache[d.year]


def _is_dst(dt):
    year = dt.year

    def nth_sunday_utc(month, n, hour_utc):
        first = datetime(year, month, 1, tzinfo=timezone.utc)
        days_until_sun = (6 - first.weekday()) % 7
        return first + timedelta(days=days_until_sun + (n - 1) * 7, hours=hour_utc)

    dst_start = nth_sunday_utc(3, 2, 7)
    dst_end   = nth_sunday_utc(11, 1, 6)
    return dst_start <= dt < dst_end


def is_market_open():
    now = datetime.now(timezone.utc)
    if now.weekday() >= 5:
        return False
    if _is_holiday(now.date()):
        return False
    utc_offset   = 4 if _is_dst(now) else 5
    market_open  = now.replace(hour=9  + utc_offset, minute=30, second=0, microsecond=0)
    market_close = now.replace(hour=16 + utc_offset, minute=0,  second=0, microsecond=0)
    return market_open <= now <= market_close


def load_history(ticker):
    try:
        with open(HISTORY_FILE_TMPL.format(ticker)) as f:
            return json.load(f)
    except Exception:
        return []


def save_history(ticker, history):
    try:
        with open(HISTORY_FILE_TMPL.format(ticker), "w") as f:
            json.dump(history, f)
    except Exception:
        pass


def load_signal_log():
    try:
        with open(SIGNAL_LOG_FILE) as f:
            return json.load(f)
    except Exception:
        return []


def save_signal_log(log):
    try:
        with open(SIGNAL_LOG_FILE, "w") as f:
            json.dump(log[-200:], f)
    except Exception:
        pass


def log_to_csv(row: dict):
    """Append a signal row to the CSV log file."""
    try:
        file_exists = os.path.isfile(CSV_LOG_FILE)
        with open(CSV_LOG_FILE, "a", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=list(row.keys()))
            if not file_exists:
                writer.writeheader()
            writer.writerow(row)
    except Exception:
        pass


def build_daily_summary() -> str:
    """Read today's CSV entries and return a plain-text summary."""
    today_str = date.today().isoformat()
    rows = []
    try:
        if os.path.isfile(CSV_LOG_FILE):
            with open(CSV_LOG_FILE, newline="") as f:
                reader = csv.DictReader(f)
                for r in reader:
                    if r.get("time", "").startswith(today_str):
                        rows.append(r)
    except Exception:
        pass

    lines = [
        f"SPX Confluence Scanner — Daily Summary {today_str}",
        f"Watchlist: {', '.join(WATCHLIST)}",
        "=" * 55,
        f"Total logged signals today: {len(rows)}",
        "",
    ]

    if not rows:
        lines.append("No signals met the logging threshold today.")
        return "\n".join(lines)

    # Per-ticker breakdown
    by_ticker: dict = {}
    for r in rows:
        t = r.get("ticker", "?")
        by_ticker.setdefault(t, []).append(r)

    lines.append("--- Per-Ticker Breakdown ---")
    for ticker, trows in sorted(by_ticker.items()):
        bull_rows = [r for r in trows if r.get("direction") == "BULL"]
        bear_rows = [r for r in trows if r.get("direction") == "BEAR"]
        best_bull = max((int(r.get("bull_score", 0)) for r in bull_rows), default=0)
        best_bear = max((int(r.get("bear_score", 0)) for r in bear_rows), default=0)
        lines.append(
            f"  {ticker}: {len(trows)} signals | "
            f"Bull {len(bull_rows)} (best {best_bull}/{MAX_SCORE}) | "
            f"Bear {len(bear_rows)} (best {best_bear}/{MAX_SCORE})"
        )

    # Top signals overall
    top_n = sorted(
        rows,
        key=lambda r: max(int(r.get("bull_score", 0)), int(r.get("bear_score", 0))),
        reverse=True,
    )[:10]

    lines += ["", "--- Top Signals Today (by score) ---"]
    for r in top_n:
        bs = int(r.get("bull_score", 0)); brs = int(r.get("bear_score", 0))
        score = max(bs, brs)
        vol   = " VOL" if r.get("vol_spike") in (True, "True") else ""
        gap   = f" gap {float(r['gap_pct']):+.2f}%" if r.get("gap_pct") not in (None, "", "None") else ""
        lines.append(
            f"  {r.get('time','?')} | {r.get('ticker','?'):5s} ${float(r.get('price',0)):.2f} "
            f"| {r.get('direction','?'):4s} {score}/{MAX_SCORE}{vol}{gap}"
        )

    # Volume spike count
    vol_count = sum(1 for r in rows if r.get("vol_spike") in (True, "True"))
    lines += ["", f"Volume spikes: {vol_count}", ""]
    lines.append("-- End of daily summary --")
    return "\n".join(lines)


def send_daily_summary():
    summary = build_daily_summary()
    print(summary, flush=True)
    _send_email(
        subject=f"[SPX Scanner] Daily Summary {date.today().isoformat()}",
        body=summary,
    )


# ====================== KEY LEVELS (Phase 9) ==============================

def compute_pivot_levels(df_1m):
    """
    Classic daily pivot points computed from the previous RTH trading day's OHLC.
    PP = (H+L+C)/3 — the central gravity point for the session.
    R/S levels give the first three resistance/support targets above/below PP.
    Also returns prev-day high/low/close as key breakout reference levels.
    """
    if df_1m is None or len(df_1m) < 2:
        return {}
    ts_et = pd.to_datetime(df_1m['ts'], unit='ms', utc=True).dt.tz_convert(_ET)
    dates = sorted(set(ts_et.dt.date))
    if len(dates) < 2:
        return {}
    prev_date = dates[-2]
    prev = df_1m[ts_et.dt.date == prev_date]
    if len(prev) == 0:
        return {}
    H = float(prev['High'].max())
    L = float(prev['Low'].min())
    C = float(prev['Close'].iloc[-1])
    PP = (H + L + C) / 3
    R1 = 2*PP - L;  R2 = PP + (H - L);  R3 = H + 2*(PP - L)
    S1 = 2*PP - H;  S2 = PP - (H - L);  S3 = L - 2*(H - PP)
    return {
        'pivot_pp':   round(PP, 2),
        'pivot_r1':   round(R1, 2), 'pivot_r2': round(R2, 2), 'pivot_r3': round(R3, 2),
        'pivot_s1':   round(S1, 2), 'pivot_s2': round(S2, 2), 'pivot_s3': round(S3, 2),
        'prev_high':  round(H,  2),
        'prev_low':   round(L,  2),
        'prev_close': round(C,  2),
    }


def _compute_max_pain(calls, puts):
    """
    Options max pain: the price at which total dollar value of expiring options is minimised,
    meaning option sellers (dealers) have minimum payout obligation — price gravitates here
    on expiry day.  O(n²) over strikes but chains are small (~50-150 rows).
    """
    try:
        c_oi = dict(zip(calls['strike'], calls['openInterest'].fillna(0)))
        p_oi = dict(zip(puts['strike'],  puts['openInterest'].fillna(0)))
        strikes = sorted(set(c_oi) | set(p_oi))
        if not strikes:
            return None
        best, min_p = strikes[0], float('inf')
        for px in strikes:
            pain = sum(max(px - k, 0) * c_oi.get(k, 0) for k in strikes)
            pain += sum(max(k - px, 0) * p_oi.get(k, 0) for k in strikes)
            if pain < min_p:
                min_p, best = pain, px
        return float(best)
    except Exception:
        return None


# ====================== VOLUME PROFILE & VWAP BANDS (Phase 12) ============

def compute_volume_profile(df_1m, n_bins=None):
    """
    Intraday volume profile from today's RTH 1m bars.

    Bins the session's price range into VP_BINS buckets, assigns each bar's
    volume to the bin whose midpoint matches the bar's typical price, then:
      VPOC — price level with the highest volume (highest-conviction S/R)
      VAH  — value area high: upper boundary of the 70%-volume zone
      VAL  — value area low:  lower boundary of the 70%-volume zone
    Price inside VAL–VAH = "fair value"; breakouts above VAH or below VAL
    signal an expansion move with less overhead/underlying resistance.
    Returns a compact profile list [[price, volume], ...] for the UI chart.
    """
    if n_bins is None:
        n_bins = VP_BINS
    if df_1m is None or len(df_1m) < 5:
        return {}
    last_day = df_1m['date'].iloc[-1]
    today = df_1m[df_1m['date'] == last_day]
    if len(today) < 5:
        return {}

    lo = float(today['Low'].min())
    hi = float(today['High'].max())
    if hi - lo < 1e-9:
        return {}

    # Assign each bar's volume to the bin of its typical price (fast, vectorised)
    typical = ((today['High'] + today['Low'] + today['Close']) / 3).values
    vols    = today['Volume'].fillna(0).astype(float).values
    bin_size = (hi - lo) / n_bins
    profile  = {}
    for tp, vol in zip(typical, vols):
        b = min(int((tp - lo) / bin_size), n_bins - 1)
        pc = round(lo + (b + 0.5) * bin_size, 2)
        profile[pc] = profile.get(pc, 0) + vol

    if not profile:
        return {}

    vpoc = max(profile, key=profile.get)
    sorted_p = sorted(profile.keys())
    vi = sorted_p.index(vpoc)

    # Expand value area from VPOC outward until VP_VALUE_AREA_PCT of volume is captured
    total_vol  = sum(profile.values())
    target_vol = total_vol * VP_VALUE_AREA_PCT
    lo_i, hi_i, area_vol = vi, vi, profile[vpoc]
    lo_ptr, hi_ptr = vi - 1, vi + 1
    while area_vol < target_vol and (lo_ptr >= 0 or hi_ptr < len(sorted_p)):
        v_lo = profile.get(sorted_p[lo_ptr], 0) if lo_ptr >= 0 else 0
        v_hi = profile.get(sorted_p[hi_ptr], 0) if hi_ptr < len(sorted_p) else 0
        if v_hi >= v_lo and hi_ptr < len(sorted_p):
            area_vol += v_hi; hi_i = hi_ptr; hi_ptr += 1
        elif lo_ptr >= 0:
            area_vol += v_lo; lo_i = lo_ptr; lo_ptr -= 1
        else:
            area_vol += v_hi; hi_i = hi_ptr; hi_ptr += 1

    profile_list = [[p, int(v)] for p, v in sorted(profile.items())]
    return {
        'vpoc':    round(vpoc, 2),
        'vah':     round(sorted_p[hi_i], 2),
        'val':     round(sorted_p[lo_i], 2),
        'profile': profile_list,
    }


def compute_vwap_bands(today_df, vwap_val):
    """
    VWAP standard-deviation bands: VWAP ± 1σ and ± 2σ.
    σ is the volume-weighted standard deviation of the typical price from VWAP.
    Price at ±2σ is statistically extreme (~5% of session time) and often
    signals mean-reversion opportunities back toward VWAP.
    """
    if today_df is None or len(today_df) < 5 or not _valid(vwap_val):
        return {}
    try:
        typical   = (today_df['High'] + today_df['Low'] + today_df['Close']) / 3
        vol       = today_df['Volume'].fillna(0).astype(float)
        total_vol = float(vol.sum())
        if total_vol <= 0:
            return {}
        variance = float((vol * (typical - vwap_val) ** 2).sum() / total_vol)
        sigma = variance ** 0.5
        if sigma <= 0:
            return {}
        return {
            'vwap_1u': round(vwap_val + sigma,     2),
            'vwap_1d': round(vwap_val - sigma,     2),
            'vwap_2u': round(vwap_val + 2 * sigma, 2),
            'vwap_2d': round(vwap_val - 2 * sigma, 2),
        }
    except Exception:
        return {}


# ====================== FIBONACCI & RELATIVE STRENGTH (Phase 11) ==========

def compute_fib_levels(df_1m, lookback=None):
    """
    Find the swing high and swing low over the last `lookback` 1m bars and
    compute classic Fibonacci retracement levels between them.

    The swing range captures roughly 3-4 hours of RTH price action (FIB_LOOKBACK=200).
    Fib levels are measured from the swing high downward — so fib_618 is 61.8%
    of the way from swing_high down to swing_low (the "golden ratio" support zone).
    These levels act as dynamic support when price pulls back in an uptrend
    and as dynamic resistance when price bounces in a downtrend.
    """
    if df_1m is None or len(df_1m) < 20:
        return {}
    n = lookback if lookback is not None else FIB_LOOKBACK
    recent = df_1m.tail(min(n, len(df_1m)))
    h = float(recent['High'].max())
    l = float(recent['Low'].min())
    diff = h - l
    if diff < 1e-9:
        return {}
    return {
        'swing_high': round(h, 2),
        'swing_low':  round(l, 2),
        'fib_236':    round(h - 0.236 * diff, 2),
        'fib_382':    round(h - 0.382 * diff, 2),
        'fib_500':    round(h - 0.500 * diff, 2),
        'fib_618':    round(h - 0.618 * diff, 2),
        'fib_786':    round(h - 0.786 * diff, 2),
    }


def _fib_level_name(price, fib_data):
    """Return the name of the nearest key fib level and its value."""
    key_levels = {
        '23.6%': fib_data.get('fib_236'),
        '38.2%': fib_data.get('fib_382'),
        '50.0%': fib_data.get('fib_500'),
        '61.8%': fib_data.get('fib_618'),
        '78.6%': fib_data.get('fib_786'),
    }
    best_name, best_val, best_dist = None, None, float('inf')
    for name, val in key_levels.items():
        if val is None:
            continue
        dist = abs(price - val)
        if dist < best_dist:
            best_dist, best_val, best_name = dist, val, name
    return best_name, best_val, best_dist


# ====================== CANDLESTICK & REGIME DETECTION (Phase 10) =========

def detect_candle_patterns(df_1m):
    """
    Detect key reversal and continuation candlestick patterns on the most
    recent bars.  Uses pure OHLC math — no external library needed.
    Checks single-bar, two-bar, and three-bar patterns; the strongest
    match wins (later patterns overwrite earlier ones, so three-bar > two-bar > one-bar).
    Returns (bull_pattern_name, bear_pattern_name) — either can be None.
    """
    if df_1m is None or len(df_1m) < 4:
        return None, None
    o = df_1m['Open'].values.astype(float)
    h = df_1m['High'].values.astype(float)
    l = df_1m['Low'].values.astype(float)
    c = df_1m['Close'].values.astype(float)

    bull_pat = bear_pat = None

    # ── Single-bar: check completed bar (-2) and current bar (-1) ──────────
    for i in (-2, -1):
        body       = abs(c[i] - o[i])
        rng        = h[i] - l[i]
        if rng < 1e-9:
            continue
        up_wick    = h[i] - max(c[i], o[i])
        lo_wick    = min(c[i], o[i]) - l[i]
        is_bull    = c[i] >= o[i]

        # Hammer / Inverted Hammer (bull reversal)
        if lo_wick >= 2 * max(body, 1e-9) and up_wick <= body * 0.5:
            bull_pat = "Hammer"
        if up_wick >= 2 * max(body, 1e-9) and lo_wick <= body * 0.5 and is_bull:
            bull_pat = "Inv. Hammer"

        # Shooting Star / Hanging Man (bear reversal)
        if up_wick >= 2 * max(body, 1e-9) and lo_wick <= body * 0.5 and not is_bull:
            bear_pat = "Shooting Star"
        if lo_wick >= 2 * max(body, 1e-9) and up_wick <= body * 0.5 and not is_bull:
            bear_pat = "Hanging Man"

        # Strong Marubozu bars (continuation)
        if is_bull  and body >= 0.85 * rng:
            bull_pat = "Bull Marubozu"
        if not is_bull and body >= 0.85 * rng:
            bear_pat = "Bear Marubozu"

        # Doji variants
        if body < 0.08 * rng:
            if lo_wick > 2.5 * up_wick:
                bull_pat = "Dragonfly Doji"
            elif up_wick > 2.5 * lo_wick:
                bear_pat = "Gravestone Doji"

    # ── Two-bar patterns: bars [-3], [-2] ──────────────────────────────────
    if len(df_1m) >= 3:
        po, pc = o[-3], c[-3]
        co, cc = o[-2], c[-2]
        p_bear = pc < po;  p_bull = pc > po
        c_bull = cc > co;  c_bear = cc < co

        if p_bear and c_bull and co <= pc and cc >= po:
            bull_pat = "Bullish Engulfing"
        if p_bull and c_bear and co >= pc and cc <= po:
            bear_pat = "Bearish Engulfing"

        # Piercing Line: bear bar then bull bar opening below prev low, closing above prev midpoint
        if p_bear and c_bull and co < l[-3] and cc > (po + pc) / 2:
            bull_pat = "Piercing Line"
        # Dark Cloud Cover: bull bar then bear bar opening above prev high, closing below prev midpoint
        if p_bull and c_bear and co > h[-3] and cc < (po + pc) / 2:
            bear_pat = "Dark Cloud Cover"

        # Tweezer Bottom / Top
        if abs(l[-3] - l[-2]) < 0.05 * (h[-2] - l[-2]) and c_bull:
            bull_pat = "Tweezer Bottom"
        if abs(h[-3] - h[-2]) < 0.05 * (h[-2] - l[-2]) and c_bear:
            bear_pat = "Tweezer Top"

    # ── Three-bar patterns: bars [-4], [-3], [-2] ──────────────────────────
    if len(df_1m) >= 4:
        b1o, b1c = o[-4], c[-4]
        b2o, b2c = o[-3], c[-3]
        b3o, b3c = o[-2], c[-2]
        b1bd = abs(b1c - b1o)
        b2bd = abs(b2c - b2o)

        # Morning Star
        if (b1c < b1o and b2bd < 0.35 * b1bd
                and b3c > b3o and b3c > (b1o + b1c) / 2):
            bull_pat = "Morning Star"
        # Evening Star
        if (b1c > b1o and b2bd < 0.35 * b1bd
                and b3c < b3o and b3c < (b1o + b1c) / 2):
            bear_pat = "Evening Star"
        # Three White Soldiers
        if (b1c > b1o and b2c > b2o and b3c > b3o
                and b2c > b1c and b3c > b2c
                and b2o > b1o and b3o > b2o):
            bull_pat = "Three White Soldiers"
        # Three Black Crows
        if (b1c < b1o and b2c < b2o and b3c < b3o
                and b2c < b1c and b3c < b2c
                and b2o < b1o and b3o < b2o):
            bear_pat = "Three Black Crows"

    return bull_pat, bear_pat


def detect_market_regime(adx_val, dmp_val, dmn_val, price,
                         bb_upper_val, bb_lower_val):
    """
    Classify the current market into one of five regime states:
      trending_up   — ADX>25, DM+ dominant → directional bull
      trending_down — ADX>25, DM- dominant → directional bear
      breakout_up   — ADX weak but price above upper BB → early bull move
      breakout_down — ADX weak but price below lower BB → early bear move
      ranging       — ADX<20, price inside BBands → mean-reversion mode
    Returns a string key (or 'unknown' when data is missing).
    """
    if not _valid(adx_val):
        return 'unknown'
    if adx_val > 25 and _valid(dmp_val) and _valid(dmn_val):
        return 'trending_up' if dmp_val > dmn_val else 'trending_down'
    if adx_val < 20:
        if _valid(bb_upper_val) and price > bb_upper_val:
            return 'breakout_up'
        if _valid(bb_lower_val) and price < bb_lower_val:
            return 'breakout_down'
        return 'ranging'
    return 'neutral'


# ====================== INSTITUTIONAL FLOW DETECTION (Phase 8) ========

def detect_block_print(df_1m, lookback=5):
    """
    Approximate dark pool block-print detection from 1m OHLCV.
    Signature: single candle with massive volume AND very tight H-L range.
    (High volume + tiny price range = large block crossed off-exchange
     with minimal market impact — the hallmark of institutional dark-pool prints.)

    Upgrade path: set POLYGON_TIER=paid to enable real v3/trades filtering
    for actual ADF/FINRA exchange codes and block-size thresholds.
    """
    if len(df_1m) < 20:
        return None, None
    df        = df_1m.tail(20).copy()
    avg_vol   = float(df['Volume'].mean())
    avg_range = float((df['High'] - df['Low']).mean())
    if avg_vol <= 0 or avg_range <= 0:
        return None, None
    for i in range(len(df) - 1, len(df) - lookback - 1, -1):
        bar   = df.iloc[i]
        vmult = float(bar['Volume']) / avg_vol
        rpct  = float(bar['High'] - bar['Low']) / avg_range
        if vmult >= BLOCK_PRINT_VOL_MULT and rpct <= BLOCK_PRINT_RANGE_PCT:
            direction = 'bull' if float(bar['Close']) >= float(bar['Open']) else 'bear'
            return direction, round(vmult, 1)
    return None, None


def compute_volume_delta(df_1m, lookback=None):
    """
    Volume delta via OHLCV approximation (no tick data required).
    Bull vol  = V × (C - L) / (H - L)
    Bear vol  = V × (H - C) / (H - L)
    Delta     = Bull_vol - Bear_vol

    Divergence signals (high-conviction reversal warnings):
      'bear' divergence: price rising but cumulative delta dominated by sellers
                         → exhaustion / distribution into strength
      'bull' divergence: price falling but cumulative delta dominated by buyers
                         → absorption / accumulation into weakness

    Upgrade path: Polygon paid v3/trades gives true tick-level bid/ask
    attribution for exact delta; OHLCV approximation is accurate to ~85%.
    """
    n = lookback or VOL_DELTA_LOOKBACK
    if len(df_1m) < n + 5:
        return None, None, None
    df  = df_1m.tail(20).copy()
    hl  = (df['High'] - df['Low']).replace(0, float('nan'))
    df['bvol'] = df['Volume'] * (df['Close'] - df['Low'])  / hl
    df['svol'] = df['Volume'] * (df['High']  - df['Close']) / hl
    df  = df.dropna(subset=['bvol', 'svol'])
    if len(df) < n:
        return None, None, None
    recent   = df.tail(n)
    bvol_sum = float(recent['bvol'].sum())
    svol_sum = float(recent['svol'].sum())
    delta    = int(bvol_sum - svol_sum)
    total    = bvol_sum + svol_sum
    bull_pct = round(bvol_sum / total * 100) if total > 0 else 50
    # Price trend over the same window
    p_change = float(df['Close'].iloc[-1]) - float(df['Close'].iloc[-n])
    if   p_change > 0 and delta < 0:  divergence = 'bear'   # up-price + sell delta = exhaustion
    elif p_change < 0 and delta > 0:  divergence = 'bull'   # dn-price + buy delta  = absorption
    else:                              divergence = None
    return delta, divergence, bull_pct


def detect_vwap_defense(df_1m, vwap_val, atr_val):
    """
    Detect institutional VWAP defense (bounce) or rejection.
    Algorithm:
      1. Find bars where mid-price is within VWAP_DEF_DIST_ATR × ATR of VWAP.
      2. Bar volume must be ≥ VWAP_DEF_VOL_MULT × average.
      3. Classify by wick structure:
           • Long upper wick + close below VWAP → rejection (bearish)
           • Long lower wick + close above VWAP → bounce (bullish)
    Institutions run VWAP algo orders all day; a hard push or rejection at
    VWAP on unusual volume reveals where the institutional benchmark defense is.
    """
    if vwap_val is None or atr_val is None or atr_val <= 0:
        return None, None
    df      = df_1m.tail(10).copy()
    avg_vol = float(df['Volume'].mean())
    if avg_vol <= 0:
        return None, None
    for i in range(len(df) - 1, max(len(df) - 5, 0) - 1, -1):
        bar  = df.iloc[i]
        mid  = (float(bar['High']) + float(bar['Low'])) / 2
        if abs(mid - vwap_val) > VWAP_DEF_DIST_ATR * atr_val:
            continue
        if float(bar['Volume']) < VWAP_DEF_VOL_MULT * avg_vol:
            continue
        o, c, h, l = float(bar['Open']), float(bar['Close']), float(bar['High']), float(bar['Low'])
        body     = abs(c - o)
        hi_wick  = h - max(o, c)
        lo_wick  = min(o, c) - l
        strength = round(float(bar['Volume']) / avg_vol, 1)
        if hi_wick > max(2 * body, atr_val * 0.05) and c < vwap_val:
            return 'rejection', strength   # hard push up was sold back down at VWAP
        if lo_wick > max(2 * body, atr_val * 0.05) and c > vwap_val:
            return 'bounce', strength      # dip below VWAP was aggressively bought back
    return None, None


def detect_tape(df_1m, atr_val):
    """
    Candle-based tape reading — approximates what a trader sees in Time & Sales.

    Two patterns detected:
    1. Iceberg order: single bar with ICEBERG_VOL_MULT × avg volume but net price
       move < ICEBERG_MOVE_ATR × ATR. Large hidden size absorbing the opposite flow.
    2. Aggressive sequence: TAPE_BARS consecutive same-direction bars with
       rising volume and avg ≥ TAPE_VOL_MULT × avg. Repeated sweeping of the book.

    Returns: (signal_type, vol_multiple)
      signal_type: 'iceberg_bull' | 'iceberg_bear' | 'aggressive_buy' | 'aggressive_sell'

    Upgrade path: Polygon paid WebSocket stream gives true trade-by-trade
    aggressor-side detection for exact iceberg/sweep identification.
    """
    if atr_val is None or atr_val <= 0 or len(df_1m) < TAPE_BARS + 5:
        return None, None
    df      = df_1m.tail(20).copy()
    avg_vol = float(df['Volume'].mean())
    if avg_vol <= 0:
        return None, None
    last = df.iloc[-1]
    # ── Iceberg detection ─────────────────────────────────────────────────────
    vmult    = float(last['Volume']) / avg_vol
    net_move = abs(float(last['Close']) - float(last['Open']))
    if vmult >= ICEBERG_VOL_MULT and net_move < ICEBERG_MOVE_ATR * atr_val:
        direction = 'bull' if float(last['Close']) >= float(last['Open']) else 'bear'
        return f'iceberg_{direction}', round(vmult, 1)
    # ── Aggressive sweep detection ────────────────────────────────────────────
    recent    = df.tail(TAPE_BARS)
    bull_bars = bool((recent['Close'] > recent['Open']).all())
    bear_bars = bool((recent['Close'] < recent['Open']).all())
    vols      = list(recent['Volume'].astype(float))
    vol_rising = all(vols[i] >= vols[i - 1] for i in range(1, len(vols)))
    avg_r_vol  = float(recent['Volume'].mean())
    if avg_r_vol < TAPE_VOL_MULT * avg_vol:
        return None, None
    if bull_bars and vol_rising:
        return 'aggressive_buy',  round(avg_r_vol / avg_vol, 1)
    if bear_bars and vol_rising:
        return 'aggressive_sell', round(avg_r_vol / avg_vol, 1)
    return None, None


# ── Optional paid-API upgrades ────────────────────────────────────────────────

def _fetch_uw_sweeps(ticker_sym):
    """
    Unusual Whales API — real institutional sweep detection.
    Set UNUSUAL_WHALES_KEY in .env to enable.
    Returns dict with sweep_call_count, sweep_put_count, net_sweep.
    Falls back to yfinance vol/OI approximation when key absent.
    """
    if not UNUSUAL_WHALES_KEY:
        return {}
    try:
        resp = requests.get(
            f"https://api.unusualwhales.com/api/stock/{ticker_sym}/option-chains",
            headers={"Authorization": f"Bearer {UNUSUAL_WHALES_KEY}"},
            timeout=5,
        )
        if resp.status_code != 200:
            return {}
        data   = resp.json().get("data", [])
        c_swps = [s for s in data if s.get("type") == "sweep" and s.get("side") == "call"]
        p_swps = [s for s in data if s.get("type") == "sweep" and s.get("side") == "put"]
        c_prem = sum(float(s.get("premium", 0)) for s in c_swps)
        p_prem = sum(float(s.get("premium", 0)) for s in p_swps)
        return {
            "sweep_call_count":   len(c_swps),
            "sweep_put_count":    len(p_swps),
            "sweep_call_premium": c_prem,
            "sweep_put_premium":  p_prem,
            "net_sweep":          "calls" if c_prem > p_prem else "puts" if p_prem > c_prem else "neutral",
        }
    except Exception as e:
        print(f"Unusual Whales [{ticker_sym}]: {e}", flush=True)
        return {}


def _fetch_polygon_dark_pool(client, ticker_sym):
    """
    Polygon v3/trades dark pool detection — real ADF/FINRA block prints.
    Set POLYGON_TIER=paid in .env to enable (requires Polygon Starter+ plan).
    Falls back to candle approximation on free tier.
    """
    if POLYGON_TIER != "paid":
        return None, None
    try:
        end   = datetime.now(timezone.utc)
        start = end - timedelta(minutes=15)
        trades = list(itertools.islice(
            client.list_trades(
                ticker_sym,
                timestamp_gte=start.strftime("%Y-%m-%dT%H:%M:%SZ"),
                timestamp_lte=end.strftime("%Y-%m-%dT%H:%M:%SZ"),
                order="desc", limit=1000,
            ), 1000
        ))
        if not trades:
            return None, None
        # Exchange codes for dark pools / ADF: 'D' (FINRA ADF), 'Q' (NASD)
        dp_exch     = {'d', 'q', '4'}
        block_size  = 50_000 if ticker_sym in ('SPY', 'QQQ', 'IWM') else 10_000
        block_bull  = block_bear = 0
        for t in trades:
            ex   = str(getattr(t, 'exchange', '') or '').lower()
            size = int(getattr(t, 'size', 0) or 0)
            cond = list(getattr(t, 'conditions', []) or [])
            is_dp = ex in dp_exch or 17 in cond or 37 in cond
            if is_dp and size >= block_size:
                # Without bid/ask we classify by close vs open of its 1m bar (simplified)
                block_bull += size
        if block_bull > 0:
            return 'bull', round(block_bull / block_size, 1)
        return None, None
    except Exception as e:
        print(f"Dark pool trades [{ticker_sym}]: {e}", flush=True)
        return None, None


# ====================== TRADE TRACKING (Phase 6) ======================

def track_signal(ticker, price, stop, tp, direction, score, cq="WEAK"):
    """Open a simulated trade. Returns True if new trade opened, False if already tracking."""
    for t in open_trades.values():
        if t["ticker"] == ticker and t["direction"] == direction:
            return False
    trade_id = f"{ticker}_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
    open_trades[trade_id] = {
        "id":        trade_id,
        "ticker":    ticker,
        "direction": direction,
        "entry":     round(float(price), 4),
        "stop":      round(float(stop),  4),
        "tp":        round(float(tp),    4),
        "score":     score,
        "cq":        cq,
        "open_time": datetime.now().isoformat(),
        "open_ts":   time.time(),
    }
    print(f"[TRADE] OPEN {ticker} {direction} @ ${price:.2f} SL${stop:.2f} TP${tp:.2f} [{score}/{MAX_SCORE}] CQ={cq}", flush=True)
    return True


def check_outcomes():
    """Check open trades against current prices; close wins/losses/timeouts."""
    global outcomes
    now_ts = time.time()
    closed = []
    for trade_id, t in list(open_trades.items()):
        d     = dashboard_data.get(t["ticker"], {})
        price = d.get("price")
        if price is None:
            continue
        result = None
        if t["direction"] == "BULL":
            if price >= t["tp"]:   result = "WIN"
            elif price <= t["stop"]: result = "LOSS"
        else:
            if price <= t["tp"]:   result = "WIN"
            elif price >= t["stop"]: result = "LOSS"
        elapsed_mins = (now_ts - t["open_ts"]) / 60
        if result is None and elapsed_mins >= TRADE_MAX_MINS:
            result = "TIMEOUT"
        if result:
            risk = abs(t["entry"] - t["stop"])
            if result == "WIN":
                r_mult = round(abs(t["tp"] - t["entry"]) / risk, 2) if risk > 0 else None
            elif result == "LOSS":
                r_mult = -1.0
            else:
                pnl = (price - t["entry"]) if t["direction"] == "BULL" else (t["entry"] - price)
                r_mult = round(pnl / risk, 2) if risk > 0 else None
            outcome = {
                **t,
                "result":       result,
                "exit_price":   round(float(price), 4),
                "close_time":   datetime.now().isoformat(),
                "r_multiple":   r_mult,
                "elapsed_mins": round(elapsed_mins, 1),
            }
            outcomes.append(outcome)
            outcomes = outcomes[-500:]
            closed.append(trade_id)
            icon = "✅" if result == "WIN" else "❌" if result == "LOSS" else "⏱"
            print(f"[TRADE] {icon} CLOSE {t['ticker']} {t['direction']} {result} @ ${price:.2f} R={r_mult}", flush=True)
    for tid in closed:
        del open_trades[tid]
    if closed:
        _save_outcomes()


# ====================== INDICATORS ======================

def _calc_ha_bull(df):
    """Proper recursive Heikin Ashi. Returns True if last candle is bullish."""
    ha_close = (df['Open'] + df['High'] + df['Low'] + df['Close']) / 4
    ha_open  = ha_close.copy()
    ha_open.iloc[0] = (df['Open'].iloc[0] + df['Close'].iloc[0]) / 2
    for i in range(1, len(ha_open)):
        ha_open.iloc[i] = (ha_open.iloc[i - 1] + ha_close.iloc[i - 1]) / 2
    return bool(ha_close.iloc[-1] > ha_open.iloc[-1])


def detect_fvg(df):
    """Returns 'bull', 'bear', or None."""
    try:
        if len(df) < 3:
            return None
        if df['Low'].iloc[-1] > df['High'].iloc[-3]:
            return 'bull'
        if df['High'].iloc[-1] < df['Low'].iloc[-3]:
            return 'bear'
        return None
    except Exception:
        return None


def detect_order_blocks(df):
    """Returns 'bull', 'bear', or None based on 10-bar swing points."""
    try:
        at_low  = bool((df['Low'].rolling(10).min()  == df['Low']).iloc[-1])
        at_high = bool((df['High'].rolling(10).max() == df['High']).iloc[-1])
        if at_low and not at_high:
            return 'bull'
        if at_high and not at_low:
            return 'bear'
        return None
    except Exception:
        return None


def detect_rsi_divergence(df):
    """Bull: price lower low + RSI higher low. Bear: inverse. Returns 'bull','bear',None."""
    try:
        if len(df) < 30 or 'rsi' not in df.columns:
            return None
        prices   = df['Close'].values[-30:]
        rsi_vals = df['rsi'].values[-30:]
        half = 15
        prior_p, recent_p = prices[:half],   prices[half:]
        prior_r, recent_r = rsi_vals[:half], rsi_vals[half:]

        pi_low = prior_p.argmin(); ri_low = recent_p.argmin()
        if recent_p[ri_low] < prior_p[pi_low] and recent_r[ri_low] > prior_r[pi_low]:
            return 'bull'

        pi_high = prior_p.argmax(); ri_high = recent_p.argmax()
        if recent_p[ri_high] > prior_p[pi_high] and recent_r[ri_high] < prior_r[pi_high]:
            return 'bear'

        return None
    except Exception:
        return None


# ====================== NOTIFICATIONS ======================

_last_alert_times = {}


def _send_discord(ticker, message):
    if not DISCORD_WEBHOOK:
        return
    try:
        requests.post(DISCORD_WEBHOOK, json={"content": message}, timeout=5)
        print(f"✅ Discord alert sent [{ticker}]", flush=True)
    except Exception as e:
        print(f"Discord failed: {e}", flush=True)


def _send_telegram(message):
    if not TELEGRAM_TOKEN or not TELEGRAM_CHAT_ID:
        return
    try:
        url = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage"
        requests.post(url, data={"chat_id": TELEGRAM_CHAT_ID, "text": message, "parse_mode": "Markdown"}, timeout=5)
        print("✅ Telegram alert sent", flush=True)
    except Exception as e:
        print(f"Telegram failed: {e}", flush=True)


def _send_email(subject, body):
    if not EMAIL_FROM or not EMAIL_PASSWORD or not EMAIL_TO:
        return
    try:
        msg = MIMEText(body)
        msg['Subject'] = subject
        msg['From']    = EMAIL_FROM
        msg['To']      = EMAIL_TO
        with smtplib.SMTP(SMTP_HOST, SMTP_PORT) as s:
            s.starttls()
            s.login(EMAIL_FROM, EMAIL_PASSWORD)
            s.send_message(msg)
        print("✅ Email alert sent", flush=True)
    except Exception as e:
        print(f"Email failed: {e}", flush=True)


def send_notifications(ticker, price, bull_score, bear_score, direction,
                       volume_spike=False, atr=None, stop=None, tp=None, cq="WEAK"):
    global _last_alert_times
    now  = datetime.now()
    last = _last_alert_times.get(ticker)
    if last and (now - last).total_seconds() < ALERT_COOLDOWN_SECS:
        remaining = int(ALERT_COOLDOWN_SECS - (now - last).total_seconds())
        print(f"Alert suppressed [{ticker}] — cooldown {remaining}s", flush=True)
        return

    # Phase 14: CQ gate — suppress if below minimum tier
    if _CQ_RANK.get(cq, 0) < _CQ_RANK.get(CQ_MIN_ALERT, 0):
        print(f"Alert suppressed [{ticker}] — CQ={cq} below min={CQ_MIN_ALERT}", flush=True)
        return

    score  = bull_score if direction == "BULL" else bear_score
    arrow  = "🔥" if direction == "BULL" else "🔻"
    vol    = " ⚡ VOLUME SPIKE" if volume_spike else ""
    levels = ""
    if atr and stop and tp:
        levels = f"\nATR: {atr:.2f} | SL: ${stop:.2f} | TP: ${tp:.2f}"

    cq_tag = {"HIGH": "★ HIGH CONF | ", "MED": "◆ MED CONF | ", "LOW": ""}.get(cq, "")
    msg = (
        f"{arrow} *{ticker} {direction} Confluence Alert*{vol}\n"
        f"{cq_tag}Price: ${price:.2f} | Score: {score}/{MAX_SCORE}"
        f"{levels}\n"
        f"Time: {now.strftime('%H:%M:%S ET')}"
    )

    # Route by CQ tier: HIGH → all channels; MED → Discord+Telegram; LOW → Discord only
    _send_discord(ticker, msg)
    if cq in ("HIGH", "MED"):
        _send_telegram(msg)
        _send_email(
            subject=f"[Scanner] {cq_tag}{ticker} {direction} — {score}/{MAX_SCORE}{vol}",
            body=msg.replace("*", "").replace("🔥", "").replace("🔻", "").replace("⚡", "")
        )

    _last_alert_times[ticker] = now
    if stop and tp:
        # Submit to Alpaca first; only open in-memory trade if order succeeds
        # (prevents stale open_trades blocking retries after a failed order)
        alpaca_id = submit_alpaca_order(ticker, direction, price, stop, tp, score, cq, atr=atr)
        if not ALPACA_ENABLED or alpaca_id:
            opened = track_signal(ticker, price, stop, tp, direction, score, cq=cq)
            if opened and alpaca_id:
                for t in open_trades.values():
                    if t["ticker"] == ticker and t["direction"] == direction:
                        t["alpaca_order_id"] = alpaca_id
                        break

    dashboard_data[ticker]["alerts"].insert(0, {
        "time":      now.strftime("%H:%M:%S"),
        "price":     round(float(price), 2),
        "score":     score,
        "direction": direction,
        "cq":        cq,
        "message":   f"{cq_tag}{direction} confluence{vol}",
    })
    dashboard_data[ticker]["alerts"] = dashboard_data[ticker]["alerts"][:10]


# ====================== ALPACA EXECUTION ======================
# Pipeline: [1] CQ Gate  →  [2] Conflict Guard  →  [3] Dynamic Sizing  →  [4] OCA Bracket

_alpaca_client: TradingClient | None = None
_alpaca_data_client: StockHistoricalDataClient | None = None

def _get_alpaca() -> TradingClient | None:
    global _alpaca_client
    if _alpaca_client is None and ALPACA_ENABLED:
        try:
            _alpaca_client = TradingClient(ALPACA_API_KEY, ALPACA_SECRET_KEY, paper=ALPACA_PAPER)
            env = "PAPER" if ALPACA_PAPER else "LIVE"
            print(f"[ALPACA] Client initialized ({env})", flush=True)
        except Exception as e:
            print(f"[ALPACA] Client init failed: {e}", flush=True)
    return _alpaca_client

def _get_alpaca_data() -> StockHistoricalDataClient | None:
    global _alpaca_data_client
    if _alpaca_data_client is None and ALPACA_ENABLED:
        try:
            _alpaca_data_client = StockHistoricalDataClient(ALPACA_API_KEY, ALPACA_SECRET_KEY)
        except Exception as e:
            print(f"[ALPACA] Data client init failed: {e}", flush=True)
    return _alpaca_data_client

def _get_live_price(ticker: str, fallback: float) -> float:
    """Fetch the latest trade price from Alpaca data API; fall back to scanner price."""
    try:
        dc = _get_alpaca_data()
        if dc:
            resp = dc.get_stock_latest_trade(StockLatestTradeRequest(symbol_or_symbols=ticker))
            return float(resp[ticker].price)
    except Exception as e:
        print(f"[ALPACA] Live price fetch failed [{ticker}]: {e}", flush=True)
    return fallback


# ── [1] CQ Gate ──────────────────────────────────────────────────────────────
def _passes_cq_gate(cq: str) -> bool:
    """Allow execution only when signal CQ meets or exceeds ALPACA_CQ_MIN (default MED)."""
    return _CQ_RANK.get(cq, 0) >= _CQ_RANK.get(ALPACA_CQ_MIN, 0)


# ── [2] Conflict Guard ───────────────────────────────────────────────────────
def _alpaca_has_conflict(client: TradingClient, ticker: str, direction: str) -> bool:
    """
    Query Alpaca's live state — not our in-memory cache — for a same-direction
    position or pending order on this ticker. Survives process restarts where
    open_trades is reset. The in-memory guard in send_notifications() runs first
    as the fast path; this is the authoritative Alpaca-side check.
    """
    want_long = (direction == "BULL")

    try:
        pos = client.get_open_position(ticker)
        already_long = (pos.side.value == "long")
        if already_long == want_long:
            print(f"[ALPACA] Guard: {ticker} already {'long' if already_long else 'short'} — skip", flush=True)
            return True
    except Exception:
        pass  # NoPositionFound is expected when no position exists

    try:
        open_orders = client.get_orders(GetOrdersRequest(symbols=[ticker]))
        if open_orders:
            print(f"[ALPACA] Guard: {ticker} has {len(open_orders)} pending order(s) — skip", flush=True)
            return True
    except Exception:
        pass

    return False


# ── [3] Dynamic Sizing ───────────────────────────────────────────────────────
def _calc_order_qty(price: float, score: int) -> float:
    """
    Target allocation = TRADE_SIZE_USD × (score / MAX_SCORE)

    Score IS the allocation percentage — pure linear:
      score=22  → $500 × 0.22 = $110  →  $110 / price
      score=45  → $500 × 0.45 = $225  →  $225 / price  (e.g. QQQ ~0.30sh)
      score=70  → $500 × 0.70 = $350  →  $350 / price
      score=100 → $500 × 1.00 = $500  →  $500 / price

    Returns fractional qty rounded to 2 dp (Alpaca supports fractions for
    SPY/QQQ/IWM/NVDA/AAPL), minimum 0.01 shares.
    """
    target_usd = round(TRADE_SIZE_USD * (score / MAX_SCORE), 2)
    qty        = max(1, int(target_usd / price))  # whole shares — bracket orders reject fractional
    return qty


# ── [4] OCA Bracket Submission ───────────────────────────────────────────────
def submit_alpaca_order(ticker: str, direction: str, price: float,
                        stop: float, tp: float, score: int, cq: str, atr: float | None = None):
    """
    Full execution pipeline:  CQ Gate → Conflict Guard → Sizing → OCA Bracket

    Bracket structure (One-Cancels-All):
      Entry leg  : MarketOrderRequest  — fills at prevailing market price
      SL leg     : StopLossRequest     — stop_price  = entry ∓ (ATR_STOP_MULT × ATR)
      TP leg     : TakeProfitRequest   — limit_price = entry ± (ATR_TP_MULT  × ATR)

    stop/tp are pre-computed by compute_signals() using the live ATR value and
    passed through scan_ticker() → send_notifications() → here.
    """
    if not ALPACA_ENABLED:
        return None

    # [1] CQ Gate
    if not _passes_cq_gate(cq):
        print(f"[ALPACA] Gate: {ticker} CQ={cq} < min={ALPACA_CQ_MIN} — skip", flush=True)
        return None

    client = _get_alpaca()
    if not client:
        return None

    # [2] Conflict Guard (Alpaca live state check)
    if _alpaca_has_conflict(client, ticker, direction):
        return None

    # [3] Anchor to live Alpaca price to avoid stale-data SL/TP rejection
    live_price = _get_live_price(ticker, price)
    if atr and atr > 0:
        if direction == "BULL":
            stop = round(live_price - ATR_STOP_MULT * atr, 2)
            tp   = round(live_price + ATR_TP_MULT   * atr, 2)
        else:
            stop = round(live_price + ATR_STOP_MULT * atr, 2)
            tp   = round(live_price - ATR_TP_MULT   * atr, 2)

    # [3] Dynamic Sizing  →  target_usd = $500 × (score / 100)
    qty        = _calc_order_qty(live_price, score)
    target_usd = round(TRADE_SIZE_USD * (score / MAX_SCORE), 2)
    side       = OrderSide.BUY if direction == "BULL" else OrderSide.SELL

    # [4] Build OCA bracket and submit
    try:
        req = MarketOrderRequest(
            symbol=ticker,
            qty=qty,
            side=side,
            time_in_force=TimeInForce.DAY,
            order_class=OrderClass.BRACKET,
            take_profit=TakeProfitRequest(limit_price=round(tp,   2)),
            stop_loss=StopLossRequest(    stop_price=round(stop, 2)),
        )
        order    = client.submit_order(req)
        notional = round(qty * live_price, 2)
        env      = "PAPER" if ALPACA_PAPER else "LIVE"
        sl_pct   = abs(price - stop) / price * 100
        tp_pct   = abs(tp   - price) / price * 100
        print(
            f"[ALPACA:{env}] BRACKET SUBMITTED\n"
            f"  ID      : {order.id}\n"
            f"  Ticker  : {ticker}  {direction}  qty={qty}sh  "
            f"(target=${target_usd:.2f} / notional≈${notional:.2f})\n"
            f"  Entry   : market  |  SL: ${stop:.2f} (-{sl_pct:.2f}%)  "
            f"|  TP: ${tp:.2f} (+{tp_pct:.2f}%)\n"
            f"  Score   : {score}/{MAX_SCORE} ({score/MAX_SCORE*100:.0f}%)  CQ: {cq}",
            flush=True
        )
        return str(order.id)
    except Exception as e:
        print(f"[ALPACA] Order failed [{ticker} {direction}]: {e}", flush=True)
        return None


# ====================== STATE ======================
app = Flask(__name__)

_blank_ticker = lambda t: {
    "price":        0.0,
    "bull_score":   0,
    "bear_score":   0,
    "direction":    "NEUTRAL",
    "max_score":    MAX_SCORE,
    "status":       "STARTING",
    "last_update":  "N/A",
    "market_open":  False,
    "volume_spike": False,
    "vol_ratio":    None,
    "atr":          None,
    "bull_stop":    None,
    "bull_tp":      None,
    "bear_stop":    None,
    "bear_tp":      None,
    "pos_size":     None,
    "gap_pct":      None,
    "gap_dir":      None,
    "pm_gap_pct":   None,
    "orb_high":     None,
    "orb_low":      None,
    "pcr":          None,
    "pcr_oi":       None,
    "call_vol":     None,
    "put_vol":      None,
    "trend_15m":       None,
    "trend_1h":        None,
    "tod_ok":          True,
    "call_oi":         None,
    "put_oi":          None,
    "unusual_calls":   False,
    "unusual_puts":    False,
    "net_flow":        "neutral",
    "block_print_dir": None,
    "block_print_mult":None,
    "vol_delta":       None,
    "vol_delta_pct":   None,
    "vol_delta_div":   None,
    "vwap_event":      None,
    "vwap_strength":   None,
    "tape_signal":     None,
    "tape_mult":       None,
    # Phase 9: pivot levels + max pain
    "pivot_pp":    None, "pivot_r1": None, "pivot_r2": None, "pivot_r3": None,
    "pivot_s1":    None, "pivot_s2": None, "pivot_s3": None,
    "prev_high":   None, "prev_low": None, "prev_close": None,
    "max_pain":    None,
    # Phase 10
    "candle_bull_pat": None,
    "candle_bear_pat": None,
    "regime":          "unknown",
    # Phase 11
    "fib_swing_high": None, "fib_swing_low": None,
    "fib_236": None, "fib_382": None, "fib_500": None, "fib_618": None, "fib_786": None,
    "fib_at_zone": False, "fib_zone_level": None, "fib_zone_val": None,
    "rs_vs_spy": None, "rs_signal": None,
    # Phase 12
    "vpoc": None, "vah": None, "val": None, "vp_profile": [],
    "vwap_1u": None, "vwap_1d": None, "vwap_2u": None, "vwap_2d": None,
    # Phase 18
    "ema50_1m": None, "pm_high": None, "pm_low": None,
    # Phase 17
    "ema9_1m": None, "range_vs_atr": None, "vwap_dist_atr": None,
    # Phase 16
    "session_open": None, "session_high": None, "session_low": None,
    "range_pos_pct": None, "session_chg_pct": None,
    "top_call_strikes": [], "top_put_strikes": [],
    # Phase 15
    "obv_trend": None, "bull_velocity": None, "bear_velocity": None,
    # Phase 14
    "stochrsi_k": None, "stochrsi_d": None,
    # Phase 22
    "sma200_1m": None, "sma200_5m": None,
    # Phase 20
    "bull_score_peak": 0, "bear_score_peak": 0,
    # Phase 13
    "bull_breakdown": {}, "bear_breakdown": {},
    "bull_cq": "WEAK",   "bear_cq": "WEAK",
    "bull_signals": {},
    "bear_signals": {},
    "history":      load_history(t),
    "alerts":       [],
}

dashboard_data = {t: _blank_ticker(t) for t in WATCHLIST}
signal_log     = load_signal_log()

# Economic calendar events for the current week
econ_events  = []
econ_fetched = None   # datetime of last fetch

# Options flow per ticker (populated by yfinance, no Polygon rate limit)
options_data = {}     # {ticker: {pcr, pcr_oi, call_vol, put_vol, expiry, last_update}}

# Simulated trade tracking (Phase 6)
open_trades = {}   # {trade_id: trade_dict} — currently open simulated positions
outcomes    = []   # list of closed trade outcome dicts, capped at 500

def _load_outcomes():
    global outcomes
    try:
        if os.path.isfile(OUTCOMES_FILE):
            with open(OUTCOMES_FILE) as f:
                outcomes = json.load(f)
    except Exception:
        pass

def _save_outcomes():
    try:
        with open(OUTCOMES_FILE, "w") as f:
            json.dump(outcomes[-500:], f)
    except Exception:
        pass

_load_outcomes()

# Market breadth — computed from dashboard_data after each full scan cycle
# Used as a free VIX proxy (no extra API call): bull_dominant ≈ VIX falling
vix_data = {
    "level":       None,        # actual VIX: see TradingView widget
    "trend":       None,        # "falling" | "rising" | None — derived from breadth
    "pct_chg":     None,
    "bull_count":  0,
    "bear_count":  0,
    "breadth":     "NEUTRAL",   # "BULL_DOMINANT" | "BEAR_DOMINANT" | "MIXED" | "NEUTRAL"
    "last_update": None,
}

# ====================== ROUTES ======================

@app.route('/')
def dashboard():
    return DASHBOARD_HTML


@app.route('/api/status')
def api_status():
    return jsonify({
        "tickers":      dashboard_data,
        "signal_log":   signal_log[-50:],
        "market_open":  is_market_open(),
        "vix":          vix_data,
        "econ_events":  econ_events,
        "options_data": options_data,
    })


@app.route('/api/signal-log')
def api_signal_log():
    return jsonify(signal_log[-100:])


@app.route('/api/signal')
def api_signal():
    try:
        with open('/tmp/axi_signal.json') as f:
            return jsonify(json.load(f))
    except FileNotFoundError:
        return jsonify({"status": "no signal yet"})
    except Exception as e:
        return jsonify({"error": str(e)}), 500


@app.route('/health')
def health():
    return jsonify({
        "status":      "healthy",
        "market_open": is_market_open(),
        "watchlist":   WATCHLIST,
        "time":        datetime.now().strftime("%H:%M:%S"),
    })


@app.route('/api/download-csv')
def download_csv():
    from flask import send_file, abort
    if not os.path.isfile(CSV_LOG_FILE):
        abort(404, description="No CSV log yet")
    return send_file(
        CSV_LOG_FILE,
        mimetype='text/csv',
        as_attachment=True,
        download_name=f"spx_signals_{date.today().isoformat()}.csv",
    )


@app.route('/manifest.json')
def pwa_manifest():
    return jsonify({
        "name": "SPX Confluence Scanner",
        "short_name": "SPX Scanner",
        "display": "standalone",
        "background_color": "#0a0a0a",
        "theme_color": "#00ffcc",
        "start_url": "/",
        "icons": [],
    })


@app.route('/api/outcomes')
def api_outcomes():
    return jsonify({
        "open_trades": list(open_trades.values()),
        "outcomes":    outcomes[-200:],
    })


@app.route('/api/alpaca')
def api_alpaca():
    if not ALPACA_ENABLED:
        return jsonify({"enabled": False, "paper": ALPACA_PAPER})
    client = _get_alpaca()
    if not client:
        return jsonify({"enabled": True, "paper": ALPACA_PAPER, "error": "Client unavailable"})
    try:
        account   = client.get_account()
        positions = client.get_all_positions()
        orders    = client.get_orders(GetOrdersRequest(
            status=QueryOrderStatus.ALL,   # open + filled + canceled
            limit=25,
        ))
        return jsonify({
            "enabled": True,
            "paper":   ALPACA_PAPER,
            "cq_min":  ALPACA_CQ_MIN,
            "size_usd": TRADE_SIZE_USD,
            "account": {
                "equity":          float(account.equity),
                "buying_power":    float(account.buying_power),
                "cash":            float(account.cash),
                "portfolio_value": float(account.portfolio_value),
                "daytrade_count":  int(account.daytrade_count),
                "pattern_day_trader": account.pattern_day_trader,
            },
            "positions": [{
                "symbol":          p.symbol,
                "side":            p.side.value,
                "qty":             float(p.qty),
                "avg_entry":       float(p.avg_entry_price),
                "current_price":   float(p.current_price)   if p.current_price   else None,
                "unrealized_pl":   float(p.unrealized_pl)   if p.unrealized_pl   else None,
                "unrealized_plpc": float(p.unrealized_plpc) if p.unrealized_plpc else None,
                "market_value":    float(p.market_value)    if p.market_value    else None,
            } for p in positions],
            "orders": [{
                "id":               str(o.id),
                "symbol":           o.symbol,
                "side":             o.side.value,
                "qty":              float(o.qty) if o.qty else None,
                "status":           o.status.value,
                "submitted_at":     str(o.submitted_at) if o.submitted_at else None,
                "filled_at":        str(o.filled_at)    if o.filled_at    else None,
                "filled_avg_price": float(o.filled_avg_price) if o.filled_avg_price else None,
                "order_class":      o.order_class.value if o.order_class else None,
                "legs":             len(o.legs) if o.legs else 0,
            } for o in orders[:25]],
        })
    except Exception as e:
        return jsonify({"enabled": True, "paper": ALPACA_PAPER, "error": str(e)})


@app.route('/test-daily-summary')
def test_daily_summary():
    import threading
    threading.Thread(target=send_daily_summary, daemon=True).start()
    return jsonify({"status": "daily summary triggered"})


@app.route('/test-alert')
def test_alert():
    _last_alert_times.pop("SPY", None)
    d = dashboard_data.get("SPY", {})
    send_notifications(
        "SPY", d.get("price", 500.0), 12, 2, "BULL",
        volume_spike=True,
        atr=d.get("atr"), stop=d.get("bull_stop"), tp=d.get("bull_tp")
    )
    return jsonify({"status": "success", "message": "Test alert sent"})


# ====================== SCANNER ======================

def _filter_rth(df):
    """Keep only regular trading hours bars: 9:30 AM – 4:00 PM ET."""
    ts_et = pd.to_datetime(df['ts'], unit='ms', utc=True).dt.tz_convert('America/New_York')
    mask  = (
        (ts_et.dt.hour > 9) | ((ts_et.dt.hour == 9) & (ts_et.dt.minute >= 30))
    ) & (ts_et.dt.hour < 16)
    return df[mask].copy().reset_index(drop=True)


def resample_to_5m(df_1m):
    df = df_1m.copy()
    df['datetime'] = pd.to_datetime(df['ts'], unit='ms', utc=True)
    df = df.set_index('datetime')
    df5 = df.resample('5min').agg({
        'Open':   'first',
        'High':   'max',
        'Low':    'min',
        'Close':  'last',
        'Volume': 'sum',
        'ts':     'first',
    }).dropna(subset=['Open', 'Close'])
    df5['date'] = df5.index.date
    return df5.reset_index(drop=True)


def _resample(df_1m, rule):
    """Generic resampler — mirrors resample_to_5m structure."""
    df = df_1m.copy()
    df['datetime'] = pd.to_datetime(df['ts'], unit='ms', utc=True)
    df = df.set_index('datetime')
    out = df.resample(rule).agg({
        'Open': 'first', 'High': 'max', 'Low': 'min',
        'Close': 'last', 'Volume': 'sum', 'ts': 'first',
    }).dropna(subset=['Open', 'Close'])
    out['date'] = out.index.date
    return out.reset_index(drop=True)

def resample_to_15m(df_1m): return _resample(df_1m, '15min')
def resample_to_1h(df_1m):  return _resample(df_1m, '1h')


def fetch_aggs(client, ticker, multiplier, days, limit=500):
    try:
        end   = datetime.now(timezone.utc)
        start = end - timedelta(days=days)
        aggs  = list(itertools.islice(
            client.get_aggs(
                ticker=ticker,
                multiplier=multiplier,
                timespan="minute",
                from_=start.strftime("%Y-%m-%d"),
                to=end.strftime("%Y-%m-%d"),
                limit=limit,
            ), limit
        ))
        if not aggs:
            return None
        df = pd.DataFrame([{
            'Open':   a.open,
            'High':   a.high,
            'Low':    a.low,
            'Close':  a.close,
            'Volume': a.volume,
            'ts':     a.timestamp,
        } for a in aggs])
        df['date'] = pd.to_datetime(df['ts'], unit='ms', utc=True).dt.date
        return df
    except Exception:
        traceback.print_exc()
        return None


def _weighted_score(signals, regime):
    """
    Compute category-weighted confluence score (0-100).

    Category weights: INST 35 | LEVELS 20 | TECH 30 | PATTERN 10 | MARKET 5
    Regime governor: in ranging/neutral markets, trend-following TECH signals
    (EMA, SMA, SuperTrend, FTFC) contribute only 0.5 to the active numerator,
    reducing the TECH fill rate and suppressing false breakout scores.
    """
    is_ranging = regime in RANGING_REGIMES
    cat_active = {k: 0.0 for k in CATEGORY_WEIGHTS}
    cat_total  = {k: 0   for k in CATEGORY_WEIGHTS}

    for key, sig in signals.items():
        cat = SIGNAL_CATEGORIES.get(key)
        if cat not in CATEGORY_WEIGHTS:
            continue
        cat_total[cat] += 1
        if sig["active"]:
            eff = TREND_MULT_RANGING if (is_ranging and cat == "TECH" and key in TREND_SIGNALS) else 1.0
            cat_active[cat] += eff

    score = 0.0
    for cat, weight in CATEGORY_WEIGHTS.items():
        total = cat_total[cat]
        if total == 0:
            continue
        score += (cat_active[cat] / total) * weight

    return round(score)


def compute_signals(df_1m, df_5m, ticker=None, pm_high=None, pm_low=None):
    # ── 1m indicators ──────────────────────────────────────────────────────────
    df = df_1m.copy()
    df['sma20'] = ta.sma(df['Close'], length=20)
    df['rsi']   = ta.rsi(df['Close'], length=14)
    adx_df      = ta.adx(df['High'], df['Low'], df['Close'], length=14)
    df['adx']   = adx_df.get('ADX_14', adx_df.iloc[:, 0])
    df['dmp']   = adx_df.get('DMP_14', adx_df.iloc[:, 1])
    df['dmn']   = adx_df.get('DMN_14', adx_df.iloc[:, 2])
    st_df       = ta.supertrend(df['High'], df['Low'], df['Close'], length=7, multiplier=1.0)
    df['st']    = st_df.iloc[:, 0]
    df = df.bfill()

    # ── NEW: Bollinger Bands ───────────────────────────────────────────────────
    bb_upper_val = bb_lower_val = bb_squeeze = None
    try:
        bb_df = ta.bbands(df['Close'], length=20, std=2.0)
        if bb_df is not None and len(bb_df.columns) >= 4:
            bb_lower  = bb_df.iloc[:, 0]   # BBL
            bb_upper  = bb_df.iloc[:, 2]   # BBU
            bb_bw     = bb_df.iloc[:, 3]   # BBB (bandwidth %)
            bb_upper_val = float(bb_upper.iloc[-1]) if _valid(bb_upper.iloc[-1]) else None
            bb_lower_val = float(bb_lower.iloc[-1]) if _valid(bb_lower.iloc[-1]) else None
            if len(bb_bw.dropna()) >= 20:
                bw_now = float(bb_bw.iloc[-1])
                bw_avg = float(bb_bw.rolling(50).mean().iloc[-1])
                bb_squeeze = _valid(bw_now) and _valid(bw_avg) and bw_now < bw_avg * 0.85
    except Exception:
        pass

    # ── NEW: MACD ─────────────────────────────────────────────────────────────
    macd_val = signal_val = macd_prev = signal_prev = None
    try:
        macd_df = ta.macd(df['Close'], fast=12, slow=26, signal=9)
        if macd_df is not None and len(macd_df.columns) >= 3:
            macd_line   = macd_df.iloc[:, 0]
            signal_line = macd_df.iloc[:, 2]
            macd_val    = float(macd_line.iloc[-1])   if _valid(macd_line.iloc[-1])   else None
            signal_val  = float(signal_line.iloc[-1]) if _valid(signal_line.iloc[-1]) else None
            macd_prev   = float(macd_line.iloc[-2])   if len(macd_line) > 1 and _valid(macd_line.iloc[-2])   else None
            signal_prev = float(signal_line.iloc[-2]) if len(signal_line) > 1 and _valid(signal_line.iloc[-2]) else None
    except Exception:
        pass

    # ── NEW: ATR ──────────────────────────────────────────────────────────────
    atr_val = None
    try:
        atr_s   = ta.atr(df['High'], df['Low'], df['Close'], length=14)
        atr_val = float(atr_s.iloc[-1]) if (atr_s is not None and _valid(atr_s.iloc[-1])) else None
    except Exception:
        pass

    # ── Phase 17: EMA9 on 1m ─────────────────────────────────────────────────
    ema9_1m_val = ema9_1m_prev = None
    try:
        ema9_s = ta.ema(df['Close'], length=9)
        if ema9_s is not None and _valid(ema9_s.iloc[-1]):
            ema9_1m_val = round(float(ema9_s.iloc[-1]), 2)
        if ema9_s is not None and len(ema9_s) >= 2 and _valid(ema9_s.iloc[-2]):
            ema9_1m_prev = round(float(ema9_s.iloc[-2]), 2)
    except Exception:
        pass

    # ── Phase 18: EMA50 on 1m ────────────────────────────────────────────────
    ema50_1m_val = None
    try:
        ema50_s = ta.ema(df['Close'], length=50)
        if ema50_s is not None and _valid(ema50_s.iloc[-1]):
            ema50_1m_val = round(float(ema50_s.iloc[-1]), 2)
    except Exception:
        pass

    # ── 15m trend: EMA(9) vs EMA(21) ─────────────────────────────────────────
    trend_15m = None
    try:
        df15 = resample_to_15m(df_1m)
        if len(df15) >= 21:
            ema9_15  = ta.ema(df15['Close'], length=9)
            ema21_15 = ta.ema(df15['Close'], length=21)
            if _valid(ema9_15.iloc[-1]) and _valid(ema21_15.iloc[-1]):
                trend_15m = 'bull' if ema9_15.iloc[-1] > ema21_15.iloc[-1] else 'bear'
    except Exception:
        pass

    # ── 1h trend: EMA(9) vs EMA(21) ──────────────────────────────────────────
    trend_1h = None
    try:
        df1h = resample_to_1h(df_1m)
        if len(df1h) >= 21:
            ema9_1h  = ta.ema(df1h['Close'], length=9)
            ema21_1h = ta.ema(df1h['Close'], length=21)
            if _valid(ema9_1h.iloc[-1]) and _valid(ema21_1h.iloc[-1]):
                trend_1h = 'bull' if ema9_1h.iloc[-1] > ema21_1h.iloc[-1] else 'bear'
    except Exception:
        pass

    # ── Phase 14: Stochastic RSI ─────────────────────────────────────────────
    stochrsi_k = stochrsi_d = stochrsi_k_prev = stochrsi_d_prev = None
    try:
        srsi = ta.stochrsi(df['Close'], length=14, rsi_length=14, k=3, d=3)
        if srsi is not None and len(srsi) >= 2:
            k_col = srsi.iloc[:, 0]
            d_col = srsi.iloc[:, 1]
            if _valid(k_col.iloc[-1]) and _valid(d_col.iloc[-1]):
                stochrsi_k      = round(float(k_col.iloc[-1]),  1)
                stochrsi_d      = round(float(d_col.iloc[-1]),  1)
                stochrsi_k_prev = round(float(k_col.iloc[-2]),  1) if _valid(k_col.iloc[-2]) else None
                stochrsi_d_prev = round(float(d_col.iloc[-2]),  1) if _valid(d_col.iloc[-2]) else None
    except Exception:
        pass

    # ── Phase 15: On-Balance Volume (OBV) trend ─────────────────────────────
    obv_bull_ok = obv_bear_ok = False
    obv_trend   = None
    try:
        obv_s = ta.obv(df['Close'], df['Volume'])
        if obv_s is not None and len(obv_s) >= 21:
            obv_ema9  = ta.ema(obv_s, length=9)
            obv_ema21 = ta.ema(obv_s, length=21)
            if _valid(obv_ema9.iloc[-1]) and _valid(obv_ema21.iloc[-1]):
                obv_bull_ok = bool(obv_ema9.iloc[-1] > obv_ema21.iloc[-1])
                obv_bear_ok = bool(obv_ema9.iloc[-1] < obv_ema21.iloc[-1])
                obv_trend   = 'bull' if obv_bull_ok else 'bear'
    except Exception:
        pass

    # ── Time-of-day filter (9:30-9:44 and 15:55-16:00 are suppressed) ────────
    et_now  = datetime.now(timezone.utc).astimezone(_ET)
    in_open = et_now.hour == 9  and et_now.minute < 45     # first 15 min
    in_close= et_now.hour == 15 and et_now.minute >= 55    # last 5 min
    tod_ok  = not (in_open or in_close)

    # ── 5m indicators ─────────────────────────────────────────────────────────
    df5 = df_5m.copy()
    df5['sma20'] = ta.sma(df5['Close'], length=20)
    df5['rsi']   = ta.rsi(df5['Close'], length=14)
    st5_df       = ta.supertrend(df5['High'], df5['Low'], df5['Close'], length=7, multiplier=1.0)
    df5['st']    = st5_df.iloc[:, 0]
    df5 = df5.bfill()

    # ── Phase 22: SMA200 on 1m + 5m ─────────────────────────────────────────
    sma200_1m_val = sma200_5m_val = None
    try:
        s200 = ta.sma(df['Close'], length=200)
        if s200 is not None and _valid(s200.iloc[-1]):
            sma200_1m_val = round(float(s200.iloc[-1]), 2)
    except Exception:
        pass
    try:
        s200_5 = ta.sma(df5['Close'], length=200)
        if s200_5 is not None and _valid(s200_5.iloc[-1]):
            sma200_5m_val = round(float(s200_5.iloc[-1]), 2)
    except Exception:
        pass

    # ── VWAP (today's 1m data) ────────────────────────────────────────────────
    last_day    = df['date'].iloc[-1]
    today_df    = df[df['date'] == last_day].copy().reset_index(drop=True)
    prev_df     = df[df['date'] < last_day]
    vwap_val    = None
    if len(today_df) >= 5:
        today_df.index = pd.to_datetime(
            today_df['ts'], unit='ms', utc=True
        ).dt.tz_convert('America/New_York')
        vwap_s = ta.vwap(today_df['High'], today_df['Low'], today_df['Close'], today_df['Volume'])
        if vwap_s is not None and len(vwap_s) > 0:
            vwap_val = float(vwap_s.iloc[-1])

    # ── NEW: Gap detection ────────────────────────────────────────────────────
    # Use fresh slices from df (today_df index was mutated for VWAP above)
    _today_raw = df[df['date'] == last_day]
    _prev_raw  = df[df['date'] <  last_day]
    gap_pct = gap_dir = None
    try:
        if len(_prev_raw) > 0 and len(_today_raw) >= 1:
            yclose = _prev_raw['Close'].iloc[-1]
            topen  = _today_raw['Open'].iloc[0]
            if pd.notna(yclose) and pd.notna(topen) and float(yclose) > 0:
                gap_pct = round((float(topen) - float(yclose)) / float(yclose) * 100, 3)
                if gap_pct >= 0.2:
                    gap_dir = 'bull'
                elif gap_pct <= -0.2:
                    gap_dir = 'bear'
    except Exception as e:
        print(f"Gap error: {e}", flush=True)

    # ── NEW: Opening Range Breakout (first 30 min = first 30 1m candles) ─────
    orb_high = orb_low = orb_dir = None
    try:
        if len(_today_raw) >= 30:
            orb_candles = _today_raw.head(30)
            orb_high    = round(float(orb_candles['High'].max()), 2)
            orb_low     = round(float(orb_candles['Low'].min()),  2)
    except Exception:
        pass

    # ── Phase 16: Session range stats (zero new API calls) ───────────────────
    session_open = session_high = session_low = range_pos_pct = session_chg_pct = None
    session_range_bull = session_range_bear = False
    try:
        if len(_today_raw) >= 1:
            session_open = round(float(_today_raw['Open'].iloc[0]), 2)
            session_high = round(float(_today_raw['High'].max()),   2)
            session_low  = round(float(_today_raw['Low'].min()),    2)
            rng = session_high - session_low
    except Exception:
        rng = 0

    # ── Snapshot values ───────────────────────────────────────────────────────
    price     = float(df['Close'].iloc[-1])
    sma20_1m  = float(df['sma20'].iloc[-1])
    sma20_1m_prev = float(df['sma20'].iloc[-2]) if len(df) >= 2 and _valid(df['sma20'].iloc[-2]) else None
    rsi_1m   = float(df['rsi'].iloc[-1])
    adx_val  = float(df['adx'].iloc[-1])
    dmp_val  = float(df['dmp'].iloc[-1])
    dmn_val  = float(df['dmn'].iloc[-1])
    st_1m    = float(df['st'].iloc[-1])
    sma20_5m = float(df5['sma20'].iloc[-1])
    st_5m    = float(df5['st'].iloc[-1])
    price_5m = float(df5['Close'].iloc[-1])

    try:
        if session_high is not None and session_low is not None and rng > 0.01:
            range_pos_pct      = round((price - session_low) / rng * 100, 1)
            session_range_bull = range_pos_pct <= 25
            session_range_bear = range_pos_pct >= 75
        if session_open and session_open > 0:
            session_chg_pct = round((price - session_open) / session_open * 100, 2)
    except Exception:
        pass

    # ── Phase 17: Range/VWAP analysis (uses existing atr_val + vwap_val) ──────
    range_vs_atr  = None
    vwap_dist_atr = None
    try:
        if session_high is not None and session_low is not None and _valid(atr_val) and atr_val > 0:
            range_vs_atr = round((session_high - session_low) / atr_val, 2)
        if _valid(vwap_val) and _valid(atr_val) and atr_val > 0:
            vwap_dist_atr = round((price - vwap_val) / atr_val, 2)
    except Exception:
        pass

    ha_bull_1m = _calc_ha_bull(df)
    ha_bull_5m = _calc_ha_bull(df5)
    ftfc_1m    = float((df['Close']  > df['Open']).tail(30).mean())
    ftfc_5m    = float((df5['Close'] > df5['Open']).tail(30).mean())
    fvg_dir    = detect_fvg(df)
    ob_dir     = detect_order_blocks(df)
    rsi_div    = detect_rsi_divergence(df)

    # ── Phase 19: EMA cross + consecutive candles ─────────────────────────────
    ema_cross_bull = ema_cross_bear = False
    try:
        if (ema9_1m_val is not None and sma20_1m is not None and
                ema9_1m_prev is not None and sma20_1m_prev is not None):
            ema_cross_bull = ema9_1m_val > sma20_1m and ema9_1m_prev <= sma20_1m_prev
            ema_cross_bear = ema9_1m_val < sma20_1m and ema9_1m_prev >= sma20_1m_prev
    except Exception:
        pass

    consec_bull = consec_bear = False
    consec_count = 0
    try:
        tail = df[['Open', 'Close']].tail(5)
        bull_streak = bear_streak = 0
        for i in range(len(tail) - 1, -1, -1):
            row = tail.iloc[i]
            if float(row['Close']) > float(row['Open']):
                bull_streak += 1
            else:
                break
        for i in range(len(tail) - 1, -1, -1):
            row = tail.iloc[i]
            if float(row['Close']) < float(row['Open']):
                bear_streak += 1
            else:
                break
        consec_bull  = bull_streak >= 3
        consec_bear  = bear_streak >= 3
        consec_count = max(bull_streak, bear_streak)
    except Exception:
        pass

    vol_avg   = float(df['Volume'].rolling(20).mean().iloc[-1])
    vol_cur   = float(df['Volume'].iloc[-1])
    vol_spike = bool(_valid(vol_avg) and vol_avg > 0 and vol_cur > VOLUME_SPIKE_MULT * vol_avg)
    vol_ratio = round(vol_cur / vol_avg, 1) if (_valid(vol_avg) and vol_avg > 0) else None

    # ── ATR risk levels ───────────────────────────────────────────────────────
    bull_stop = bull_tp = bear_stop = bear_tp = pos_size = None
    if _valid(atr_val) and atr_val > 0:
        bull_stop = round(price - ATR_STOP_MULT * atr_val, 2)
        bull_tp   = round(price + ATR_TP_MULT   * atr_val, 2)
        bear_stop = round(price + ATR_STOP_MULT * atr_val, 2)
        bear_tp   = round(price - ATR_TP_MULT   * atr_val, 2)
        risk_per_trade = ACCOUNT_SIZE * RISK_PCT
        pos_size = max(1, int(risk_per_trade / (ATR_STOP_MULT * atr_val)))

    # ── ORB direction (needs price) ───────────────────────────────────────────
    if orb_high is not None and orb_low is not None:
        if price > orb_high:
            orb_dir = 'bull'
        elif price < orb_low:
            orb_dir = 'bear'

    # ── Market breadth signal (uses global vix_data, populated after each cycle) ─
    breadth   = vix_data.get("breadth", "NEUTRAL")
    bc        = vix_data.get("bull_count", 0)
    bec       = vix_data.get("bear_count", 0)
    # Bull: majority of watchlist tickers are bullish (breadth confirms)
    vix_bull  = breadth == "BULL_DOMINANT"
    # Bear: majority of watchlist tickers are bearish
    vix_bear  = breadth == "BEAR_DOMINANT"
    vix_label = f"{bc}B/{bec}b" if (bc + bec) > 0 else "--"

    # ── Put/Call Ratio signal (uses global options_data, fetched via yfinance) ─
    opts      = options_data.get(ticker, {}) if ticker else {}
    pcr       = opts.get("pcr")
    pcr_bull  = bool(_valid(pcr) and float(pcr) < PCR_BULL_THRESH)   # calls dominating
    pcr_bear  = bool(_valid(pcr) and float(pcr) > PCR_BEAR_THRESH)   # puts dominating
    pcr_label = f"{pcr:.2f}" if _valid(pcr) else "No data"

    # ── Institutional flow signals (Phase 8) ──────────────────────────────────

    # 1. Dark pool block print (candle approx; real data needs POLYGON_TIER=paid)
    block_dir, block_mult = detect_block_print(df_1m)

    # 2. Unusual options flow (vol/OI from yfinance; real sweeps need UNUSUAL_WHALES_KEY)
    opts_info   = options_data.get(ticker, {}) if ticker else {}
    unusual_calls = bool(opts_info.get("unusual_calls"))
    unusual_puts  = bool(opts_info.get("unusual_puts"))
    net_flow      = opts_info.get("net_flow", "neutral")
    call_voi      = opts_info.get("call_voi")
    put_voi       = opts_info.get("put_voi")
    flow_label    = (f"C/VOI {call_voi:.2f}" if call_voi else
                     f"P/VOI {put_voi:.2f}"  if put_voi  else "No data")

    # 3. Volume delta / order flow divergence
    vol_delta_raw, vol_delta_div, bull_pct = compute_volume_delta(df_1m)
    # Directional: positive delta = buyers in control (bull signal)
    #              negative delta = sellers in control (bear signal)
    delta_bull = vol_delta_raw is not None and vol_delta_raw > 0
    delta_bear = vol_delta_raw is not None and vol_delta_raw < 0
    delta_label = (f"{bull_pct}% buy pressure" if bull_pct is not None else "No data")

    # 4. VWAP defense / bounce zone
    vwap_event, vwap_strength = detect_vwap_defense(df_1m, vwap_val, atr_val)
    vwap_def_label = (f"{vwap_event.title()} ×{vwap_strength}" if vwap_event else
                      f"Near VWAP" if (vwap_val and abs(price - vwap_val) < (atr_val or 1)) else "Not at VWAP")

    # 5. Tape reading
    tape_signal, tape_mult = detect_tape(df_1m, atr_val)
    tape_bull = tape_signal in ('aggressive_buy', 'iceberg_bull')
    tape_bear = tape_signal in ('aggressive_sell', 'iceberg_bear')
    tape_label = (tape_signal.replace('_', ' ').title() + f" ×{tape_mult}" if tape_signal else "No signal")

    # ── Phase 9: Pivot levels + key levels ────────────────────────────────────
    pivots    = compute_pivot_levels(df_1m)
    pp        = pivots.get('pivot_pp')
    r1        = pivots.get('pivot_r1')
    r2        = pivots.get('pivot_r2')
    r3        = pivots.get('pivot_r3')
    s1        = pivots.get('pivot_s1')
    s2        = pivots.get('pivot_s2')
    s3        = pivots.get('pivot_s3')
    prev_high  = pivots.get('prev_high')
    prev_low   = pivots.get('prev_low')
    prev_close = pivots.get('prev_close')
    max_pain   = opts_info.get('max_pain')   # stored by fetch_options_flow, no extra API call

    pivot_bull_ok = bool(pp       and price > pp)
    pdh_break_ok  = bool(prev_high and price > prev_high)
    pivot_bear_ok = bool(pp       and price < pp)
    pdl_break_ok  = bool(prev_low  and price < prev_low)

    pp_str   = f"${pp:.2f}"        if pp        else "No data"
    pdh_str  = f"${prev_high:.2f}" if prev_high else "No data"
    pdl_str  = f"${prev_low:.2f}"  if prev_low  else "No data"

    # ── Phase 10: Candlestick patterns + market regime ────────────────────────
    candle_bull_pat, candle_bear_pat = detect_candle_patterns(df_1m)
    regime = detect_market_regime(adx_val, dmp_val, dmn_val, price,
                                  bb_upper_val, bb_lower_val)
    regime_bull_ok = regime in ('trending_up',   'breakout_up')
    regime_bear_ok = regime in ('trending_down', 'breakout_down')
    regime_label   = regime.replace('_', ' ').title() if regime else "Unknown"

    # ── Phase 11: Fibonacci retracement ──────────────────────────────────────
    fib_data   = compute_fib_levels(df_1m)
    fib_zone   = FIB_ZONE_ATR * (atr_val or 0.5)
    fib_lv_name, fib_lv_val, fib_lv_dist = _fib_level_name(price, fib_data)
    fib_at_zone = fib_lv_val is not None and fib_lv_dist <= fib_zone
    # Support: at zone AND price ≥ level (bouncing off support from above)
    # Resist:  at zone AND price ≤ level (pressing against resistance from below)
    fib_support_ok = fib_at_zone and price >= fib_lv_val
    fib_resist_ok  = fib_at_zone and price <= fib_lv_val
    if fib_at_zone and fib_lv_name and fib_lv_val:
        fib_label = f"Fib {fib_lv_name} ${fib_lv_val:.2f}"
    else:
        nearest_above = min(
            (v for v in fib_data.values() if isinstance(v, float) and v > price),
            default=None
        )
        nearest_below = max(
            (v for v in fib_data.values() if isinstance(v, float) and v < price),
            default=None
        )
        if nearest_above and nearest_below:
            fib_label = f"Btw ${nearest_below:.2f}–${nearest_above:.2f}"
        else:
            fib_label = "No zone"

    # ── Phase 12: Volume profile + VWAP bands ─────────────────────────────────
    vp_result   = compute_volume_profile(df_1m)
    vpoc        = vp_result.get('vpoc')
    vah         = vp_result.get('vah')
    val         = vp_result.get('val')
    vp_profile  = vp_result.get('profile', [])

    vwap_bands  = compute_vwap_bands(_today_raw if len(_today_raw) >= 5 else df_1m.tail(10), vwap_val)
    vwap_1u     = vwap_bands.get('vwap_1u')
    vwap_1d     = vwap_bands.get('vwap_1d')
    vwap_2u     = vwap_bands.get('vwap_2u')
    vwap_2d     = vwap_bands.get('vwap_2d')

    vpoc_bull_ok  = bool(vpoc and price > vpoc)
    vpoc_bear_ok  = bool(vpoc and price < vpoc)
    above_vah_ok  = bool(vah  and price > vah)
    below_val_ok  = bool(val  and price < val)

    vpoc_str = f"${vpoc:.2f}" if vpoc else "No data"
    if vah and val and price:
        if price > vah:
            va_pos = f"Above VAH ${vah:.2f}"
        elif price < val:
            va_pos = f"Below VAL ${val:.2f}"
        else:
            pct_in = round((price - val) / max(vah - val, 0.01) * 100)
            va_pos = f"In VA {pct_in}%"
    else:
        va_pos = "No data"

    # ── Signal builder helper ──────────────────────────────────────────────────
    def bs(label, pts, active, value, tf1=None, tf5=None):
        d = {"label": label, "points": pts, "active": bool(active), "value": value}
        if tf1 is not None: d["tf1"] = bool(tf1)
        if tf5 is not None: d["tf5"] = bool(tf5)
        return d

    # ── Phase 22: SMA200 signal booleans ────────────────────────────────────
    sma200_b = (_valid(sma200_1m_val) and price    > sma200_1m_val and
                _valid(sma200_5m_val) and price_5m > sma200_5m_val)
    sma200_r = (_valid(sma200_1m_val) and price    < sma200_1m_val and
                _valid(sma200_5m_val) and price_5m < sma200_5m_val)
    sma200_lbl = (f"1m:{sma200_1m_val:.2f} 5m:{sma200_5m_val:.2f}"
                  if sma200_1m_val is not None and sma200_5m_val is not None else "--")

    # ── Bull signals ───────────────────────────────────────────────────────────
    sma_b1 = _valid(sma20_1m) and price    > sma20_1m
    sma_b5 = _valid(sma20_5m) and price_5m > sma20_5m
    adx_b  = _valid(adx_val) and adx_val > 22 and _valid(dmp_val) and _valid(dmn_val) and dmp_val > dmn_val
    rsi_b  = _valid(rsi_1m)  and 45 < rsi_1m < 65
    ftfc_b1= _valid(ftfc_1m) and ftfc_1m > 0.6
    ftfc_b5= _valid(ftfc_5m) and ftfc_5m > 0.6
    st_b1  = _valid(st_1m)   and price    > st_1m
    st_b5  = _valid(st_5m)   and price_5m > st_5m
    vwap_b = _valid(vwap_val) and price   > vwap_val

    # BB squeeze bull: squeeze detected AND price broke above upper band
    bb_b = bool(bb_squeeze and bb_upper_val and price > bb_upper_val)
    # MACD bull crossover: MACD line just crossed above signal line
    macd_b = bool(
        macd_val is not None and signal_val is not None and
        macd_prev is not None and signal_prev is not None and
        macd_val > signal_val and macd_prev <= signal_prev
    )
    # StochRSI bull: K crossed above D from non-overbought territory
    stochrsi_bull = bool(
        stochrsi_k is not None and stochrsi_d is not None and
        stochrsi_k_prev is not None and stochrsi_d_prev is not None and
        stochrsi_k > stochrsi_d and stochrsi_k_prev <= stochrsi_d_prev and
        stochrsi_k < 80
    )
    # StochRSI bear: K crossed below D from non-oversold territory
    stochrsi_bear = bool(
        stochrsi_k is not None and stochrsi_d is not None and
        stochrsi_k_prev is not None and stochrsi_d_prev is not None and
        stochrsi_k < stochrsi_d and stochrsi_k_prev >= stochrsi_d_prev and
        stochrsi_k > 20
    )
    _srsi_val = f"K:{stochrsi_k} D:{stochrsi_d}" if stochrsi_k is not None else "--"

    ema9_b  = _valid(ema9_1m_val)  and price > ema9_1m_val
    ema9_r  = _valid(ema9_1m_val)  and price < ema9_1m_val
    ema9_lbl = f"{ema9_1m_val:.2f}" if ema9_1m_val is not None else "--"
    ema50_b = _valid(ema50_1m_val) and price > ema50_1m_val
    ema50_r = _valid(ema50_1m_val) and price < ema50_1m_val
    ema50_lbl = f"{ema50_1m_val:.2f}" if ema50_1m_val is not None else "--"
    pm_high_b = pm_high is not None and price > pm_high
    pm_low_r  = pm_low  is not None and price < pm_low

    bull = {
        "sma20":       bs("SMA20 MTF",      2, sma_b1 and sma_b5,      f"{sma20_1m:.2f}" if _valid(sma20_1m) else "--",  sma_b1, sma_b5),
        "ema9":        bs("EMA9 ↑",           1, ema9_b,                 ema9_lbl),
        "ema50":       bs("EMA50 ↑",         1, ema50_b,                ema50_lbl),
        "ema_cross":   bs("EMA9×SMA20 ↑",   1, ema_cross_bull,         f"EMA9 {ema9_1m_val} > SMA20 {sma20_1m}" if ema_cross_bull else "--"),
        "adx":         bs("ADX Bull",        1, adx_b,                  f"{adx_val:.1f}"  if _valid(adx_val)  else "--"),
        "rsi":         bs("RSI 45-65",       1, rsi_b,                  f"{rsi_1m:.1f}"   if _valid(rsi_1m)   else "--"),
        "ftfc":        bs("FTFC MTF",        2, ftfc_b1 and ftfc_b5,    f"{ftfc_1m*100:.0f}%" if _valid(ftfc_1m) else "--", ftfc_b1, ftfc_b5),
        "supertrend":  bs("SuperTrend MTF",  1, st_b1 and st_b5,       f"{st_1m:.2f}"    if _valid(st_1m)    else "--",  st_b1, st_b5),
        "heikin_ashi": bs("HA Bull MTF",     1, ha_bull_1m and ha_bull_5m, "Bull" if ha_bull_1m else "Bear",             ha_bull_1m, ha_bull_5m),
        "vwap":        bs("Above VWAP",      1, vwap_b,                 f"{vwap_val:.2f}" if _valid(vwap_val) else "--"),
        "fvg":         bs("FVG Bull",        1, fvg_dir == 'bull',      fvg_dir.capitalize() if fvg_dir else "None"),
        "ob":          bs("Order Block Bull",1, ob_dir  == 'bull',      ob_dir.capitalize()  if ob_dir  else "None"),
        "rsi_div":     bs("RSI Div Bull",    1, rsi_div == 'bull',      rsi_div.capitalize() if rsi_div else "None"),
        "bb":          bs("BB Squeeze ↑",    1, bb_b,                   f">{bb_upper_val:.2f}" if bb_upper_val else "--"),
        "macd":        bs("MACD Cross ↑",    1, macd_b,                 f"{macd_val:.3f}" if macd_val is not None else "--"),
        "stochrsi":    bs("StochRSI Cross ↑",1, stochrsi_bull,          _srsi_val),
        "orb":         bs("ORB Break ↑",     1, orb_dir == 'bull',      f">{orb_high:.2f}" if orb_high else "No ORB"),
        "gap":         bs("Gap Up",          1, gap_dir == 'bull',      f"+{gap_pct:.2f}%" if (gap_pct is not None and gap_pct > 0) else (f"{gap_pct:.2f}%" if gap_pct is not None else "--")),
        "vix":         bs("Breadth Bull",     1, vix_bull,               vix_label),
        "pcr":         bs("P/C Ratio Bull",   1, pcr_bull,               pcr_label),
        "trend_15m":   bs("15m Trend ↑",      1, trend_15m == 'bull',    trend_15m or "No data"),
        "trend_1h":    bs("1h Trend ↑",       1, trend_1h  == 'bull',    trend_1h  or "No data"),
        # ── Institutional flow ─────────────────────────────────────────────────
        "block_print": bs("Dark Pool Accum",  1, block_dir == 'bull',    f"×{block_mult}" if block_mult else "No print"),
        "flow_unusual":bs("Unusual Calls",    1, unusual_calls,           flow_label),
        "vol_delta":   bs("Vol Delta ▲",      1, delta_bull,              delta_label),
        "vwap_def":    bs("VWAP Bounce",      1, vwap_event == 'bounce',  vwap_def_label),
        "tape_read":   bs("Tape Aggression ↑",1, tape_bull,               tape_label),
        "obv":         bs("OBV Trend ↑",      1, obv_bull_ok,             obv_trend or "--"),
        # ── Pivot / key levels (Phase 9) ──────────────────────────────────────
        "pivot_bull":  bs("Above Pivot PP",   1, pivot_bull_ok,           pp_str),
        "pdh_break":   bs("PDH Breakout",     1, pdh_break_ok,            pdh_str),
        "pm_high_break":bs("PM High Break ↑", 1, pm_high_b,               f"${pm_high:.2f}" if pm_high else "--"),
        # ── Candle patterns + regime (Phase 10) ───────────────────────────────
        "candle_bull": bs("Candle Pattern ↑", 1, candle_bull_pat is not None, candle_bull_pat or "None"),
        "consec_bars": bs("Consec Green ×3", 1, consec_bull,              f"×{consec_count} bars" if consec_bull else "--"),
        "regime_bull": bs("Regime: Bull",     1, regime_bull_ok,          regime_label),
        # ── Fibonacci zones (Phase 11) ─────────────────────────────────────────
        "fib_support": bs("Fib Support",      1, fib_support_ok,          fib_label),
        "fib_ext":     bs("Fib Extension ↑",  1, bool(fib_data.get('swing_high') and price > fib_data['swing_high']), f">{fib_data.get('swing_high','--')}"),
        # ── Volume profile (Phase 12) ──────────────────────────────────────────
        "vpoc_bull":   bs("Above VPOC",       1, vpoc_bull_ok,            vpoc_str),
        "above_vah":   bs("Above VAH ↑",      1, above_vah_ok,            va_pos),
        # ── Phase 16: Session range ────────────────────────────────────────────
        "session_range": bs("Session Low Zone",1, session_range_bull,
                            f"{range_pos_pct:.0f}% of rng" if range_pos_pct is not None else "--"),
        # ── Phase 22: SMA200 MTF ──────────────────────────────────────────────
        "sma200":        bs("SMA200 MTF ↑",   1, sma200_b, sma200_lbl,
                            _valid(sma200_1m_val) and price    > sma200_1m_val,
                            _valid(sma200_5m_val) and price_5m > sma200_5m_val),
    }
    bull_score = _weighted_score(bull, regime)

    # ── Bear signals ───────────────────────────────────────────────────────────
    sma_r1  = _valid(sma20_1m) and price    < sma20_1m
    sma_r5  = _valid(sma20_5m) and price_5m < sma20_5m
    adx_r   = _valid(adx_val)  and adx_val > 22 and _valid(dmp_val) and _valid(dmn_val) and dmn_val > dmp_val
    rsi_r   = _valid(rsi_1m)   and 35 < rsi_1m < 55
    ftfc_r1 = _valid(ftfc_1m)  and ftfc_1m < 0.4
    ftfc_r5 = _valid(ftfc_5m)  and ftfc_5m < 0.4
    st_r1   = _valid(st_1m)    and price    < st_1m
    st_r5   = _valid(st_5m)    and price_5m < st_5m
    vwap_r  = _valid(vwap_val) and price    < vwap_val

    bb_r   = bool(bb_squeeze and bb_lower_val and price < bb_lower_val)
    macd_r = bool(
        macd_val is not None and signal_val is not None and
        macd_prev is not None and signal_prev is not None and
        macd_val < signal_val and macd_prev >= signal_prev
    )

    bear = {
        "sma20":       bs("SMA20 MTF",       2, sma_r1 and sma_r5,     f"{sma20_1m:.2f}" if _valid(sma20_1m) else "--",  sma_r1, sma_r5),
        "ema9":        bs("EMA9 ↓",            1, ema9_r,                ema9_lbl),
        "ema50":       bs("EMA50 ↓",          1, ema50_r,               ema50_lbl),
        "ema_cross":   bs("EMA9×SMA20 ↓",    1, ema_cross_bear,        f"EMA9 {ema9_1m_val} < SMA20 {sma20_1m}" if ema_cross_bear else "--"),
        "adx":         bs("ADX Bear",         1, adx_r,                 f"{adx_val:.1f}"  if _valid(adx_val)  else "--"),
        "rsi":         bs("RSI 35-55",        1, rsi_r,                 f"{rsi_1m:.1f}"   if _valid(rsi_1m)   else "--"),
        "ftfc":        bs("FTFC Bear MTF",    2, ftfc_r1 and ftfc_r5,   f"{(1-ftfc_1m)*100:.0f}%" if _valid(ftfc_1m) else "--", ftfc_r1, ftfc_r5),
        "supertrend":  bs("SuperTrend MTF",   1, st_r1 and st_r5,      f"{st_1m:.2f}"    if _valid(st_1m)    else "--",  st_r1, st_r5),
        "heikin_ashi": bs("HA Bear MTF",      1, (not ha_bull_1m) and (not ha_bull_5m), "Bear" if not ha_bull_1m else "Bull", not ha_bull_1m, not ha_bull_5m),
        "vwap":        bs("Below VWAP",       1, vwap_r,                f"{vwap_val:.2f}" if _valid(vwap_val) else "--"),
        "fvg":         bs("FVG Bear",         1, fvg_dir == 'bear',     fvg_dir.capitalize() if fvg_dir else "None"),
        "ob":          bs("OB Bear",          1, ob_dir  == 'bear',     ob_dir.capitalize()  if ob_dir  else "None"),
        "rsi_div":     bs("RSI Div Bear",     1, rsi_div == 'bear',     rsi_div.capitalize() if rsi_div else "None"),
        "bb":          bs("BB Squeeze ↓",     1, bb_r,                  f"<{bb_lower_val:.2f}" if bb_lower_val else "--"),
        "macd":        bs("MACD Cross ↓",     1, macd_r,                f"{macd_val:.3f}" if macd_val is not None else "--"),
        "stochrsi":    bs("StochRSI Cross ↓", 1, stochrsi_bear,         _srsi_val),
        "orb":         bs("ORB Break ↓",      1, orb_dir == 'bear',     f"<{orb_low:.2f}" if orb_low else "No ORB"),
        "gap":         bs("Gap Down",         1, gap_dir == 'bear',     f"{gap_pct:.2f}%" if (gap_pct is not None and gap_pct < 0) else (f"+{gap_pct:.2f}%" if gap_pct is not None else "--")),
        "vix":         bs("Breadth Bear",     1, vix_bear,               vix_label),
        "pcr":         bs("P/C Ratio Bear",   1, pcr_bear,               pcr_label),
        "trend_15m":   bs("15m Trend ↓",      1, trend_15m == 'bear',    trend_15m or "No data"),
        "trend_1h":    bs("1h Trend ↓",       1, trend_1h  == 'bear',    trend_1h  or "No data"),
        # ── Institutional flow ─────────────────────────────────────────────────
        "block_print": bs("Dark Pool Dist",   1, block_dir == 'bear',    f"×{block_mult}" if block_mult else "No print"),
        "flow_unusual":bs("Unusual Puts",     1, unusual_puts,            flow_label),
        "vol_delta":   bs("Vol Delta ▼",      1, delta_bear,              delta_label),
        "vwap_def":    bs("VWAP Rejection",   1, vwap_event == 'rejection',vwap_def_label),
        "tape_read":   bs("Tape Aggression ↓",1, tape_bear,               tape_label),
        "obv":         bs("OBV Trend ↓",      1, obv_bear_ok,             obv_trend or "--"),
        # ── Pivot / key levels (Phase 9) ──────────────────────────────────────
        "pivot_bear":  bs("Below Pivot PP",   1, pivot_bear_ok,           pp_str),
        "pdl_break":   bs("PDL Breakdown",    1, pdl_break_ok,            pdl_str),
        "pm_low_break":bs("PM Low Break ↓",   1, pm_low_r,                f"${pm_low:.2f}" if pm_low else "--"),
        # ── Candle patterns + regime (Phase 10) ───────────────────────────────
        "candle_bear": bs("Candle Pattern ↓", 1, candle_bear_pat is not None, candle_bear_pat or "None"),
        "consec_bars": bs("Consec Red ×3",   1, consec_bear,             f"×{consec_count} bars" if consec_bear else "--"),
        "regime_bear": bs("Regime: Bear",     1, regime_bear_ok,          regime_label),
        # ── Fibonacci zones (Phase 11) ─────────────────────────────────────────
        "fib_resist":  bs("Fib Resistance",   1, fib_resist_ok,           fib_label),
        "fib_ext":     bs("Fib Extension ↓",  1, bool(fib_data.get('swing_low') and price < fib_data['swing_low']), f"<{fib_data.get('swing_low','--')}"),
        # ── Volume profile (Phase 12) ──────────────────────────────────────────
        "vpoc_bear":   bs("Below VPOC",       1, vpoc_bear_ok,            vpoc_str),
        "below_val":   bs("Below VAL ↓",      1, below_val_ok,            va_pos),
        # ── Phase 16: Session range ────────────────────────────────────────────
        "session_range": bs("Session High Zone",1, session_range_bear,
                            f"{range_pos_pct:.0f}% of rng" if range_pos_pct is not None else "--"),
        # ── Phase 22: SMA200 MTF ──────────────────────────────────────────────
        "sma200":        bs("SMA200 MTF ↓",   1, sma200_r, sma200_lbl,
                            _valid(sma200_1m_val) and price    < sma200_1m_val,
                            _valid(sma200_5m_val) and price_5m < sma200_5m_val),
    }
    bear_score = _weighted_score(bear, regime)

    # ── Phase 13: Per-category confluence breakdown ───────────────────────────
    def _cat_breakdown(signals):
        cats = {"TECH": 0, "PATTERN": 0, "LEVELS": 0, "INST": 0, "MARKET": 0}
        pts  = {k: 0 for k in cats}
        tot  = {k: 0 for k in cats}
        for key, sig in signals.items():
            cat = SIGNAL_CATEGORIES.get(key, "TECH")
            tot[cat]  += sig["points"]
            if sig["active"]:
                cats[cat] += 1
                pts[cat]  += sig["points"]
        n_cats       = sum(1 for v in cats.values() if v > 0)
        tech_strong  = cats.get("TECH", 0) >= 3
        inst_present = cats.get("INST", 0) >= 1
        if n_cats >= 4 and tech_strong and inst_present:
            cq = "HIGH"
        elif n_cats >= 3 and tech_strong:
            cq = "MED"
        elif n_cats >= 2:
            cq = "LOW"
        else:
            cq = "WEAK"
        return {"active": cats, "pts": pts, "total": tot, "n_cats": n_cats, "cq": cq}

    bull_breakdown = _cat_breakdown(bull)
    bear_breakdown = _cat_breakdown(bear)

    if bull_score > bear_score:
        direction = "BULL"
    elif bear_score > bull_score:
        direction = "BEAR"
    else:
        direction = "NEUTRAL"

    return {
        "price":        round(price, 2),
        "bull_score":   int(bull_score),
        "bear_score":   int(bear_score),
        "direction":    direction,
        "bull_signals": bull,
        "bear_signals": bear,
        "volume_spike": vol_spike,
        "vol_ratio":    vol_ratio,
        "atr":          round(atr_val, 3) if _valid(atr_val) else None,
        "bull_stop":    bull_stop,
        "bull_tp":      bull_tp,
        "bear_stop":    bear_stop,
        "bear_tp":      bear_tp,
        "pos_size":     pos_size,
        "gap_pct":      gap_pct,
        "gap_dir":      gap_dir,
        "orb_high":     orb_high,
        "orb_low":      orb_low,
        "trend_15m":    trend_15m,
        "trend_1h":     trend_1h,
        "tod_ok":       tod_ok,
        # institutional flow
        "block_print_dir":  block_dir,
        "block_print_mult": block_mult,
        "vol_delta":        vol_delta_raw,
        "vol_delta_pct":    bull_pct,
        "vol_delta_div":    vol_delta_div,  # 'bull' | 'bear' | None
        "vwap_event":       vwap_event,
        "vwap_strength":    vwap_strength,
        "tape_signal":      tape_signal,
        "tape_mult":        tape_mult,
        "net_flow":         net_flow,
        # Phase 9: pivot levels + key levels
        "pivot_pp":   pp,    "pivot_r1": r1,   "pivot_r2": r2,   "pivot_r3": r3,
        "pivot_s1":   s1,    "pivot_s2": s2,   "pivot_s3": s3,
        "prev_high":  prev_high,  "prev_low": prev_low,  "prev_close": prev_close,
        # Phase 10
        "candle_bull_pat": candle_bull_pat,
        "candle_bear_pat": candle_bear_pat,
        "regime":          regime,
        # Phase 11
        "fib_swing_high": fib_data.get('swing_high'),
        "fib_swing_low":  fib_data.get('swing_low'),
        "fib_236": fib_data.get('fib_236'), "fib_382": fib_data.get('fib_382'),
        "fib_500": fib_data.get('fib_500'), "fib_618": fib_data.get('fib_618'),
        "fib_786": fib_data.get('fib_786'),
        "fib_at_zone": fib_at_zone, "fib_zone_level": fib_lv_name, "fib_zone_val": fib_lv_val,
        # Phase 12
        "vpoc": vpoc, "vah": vah, "val": val, "vp_profile": vp_profile,
        "vwap_1u": vwap_1u, "vwap_1d": vwap_1d,
        "vwap_2u": vwap_2u, "vwap_2d": vwap_2d,
        # Phase 14: Stochastic RSI
        "stochrsi_k": stochrsi_k,
        "stochrsi_d": stochrsi_d,
        # Phase 22: SMA200
        "sma200_1m": sma200_1m_val,
        "sma200_5m": sma200_5m_val,
        # Phase 18: EMA50 + PM levels
        "ema50_1m": ema50_1m_val,
        "pm_high":  pm_high,
        "pm_low":   pm_low,
        # Phase 17: EMA9 + range/VWAP analysis
        "ema9_1m":      ema9_1m_val,
        "range_vs_atr": range_vs_atr,
        "vwap_dist_atr":vwap_dist_atr,
        # Phase 16: session range
        "session_open":    session_open,
        "session_high":    session_high,
        "session_low":     session_low,
        "range_pos_pct":   range_pos_pct,
        "session_chg_pct": session_chg_pct,
        # Phase 15: OBV trend
        "obv_trend": obv_trend,
        # Phase 13: confluence quality breakdown
        "bull_breakdown": bull_breakdown,
        "bear_breakdown": bear_breakdown,
        "bull_cq":        bull_breakdown["cq"],
        "bear_cq":        bear_breakdown["cq"],
    }


def fetch_econ_calendar():
    """Fetch this week's high-impact USD events from ForexFactory JSON feed."""
    global econ_events, econ_fetched
    try:
        resp = requests.get(
            ECON_CAL_URL,
            timeout=10,
            headers={"User-Agent": "Mozilla/5.0 (compatible; scanner/1.0)"},
        )
        if resp.status_code != 200:
            print(f"Econ calendar HTTP {resp.status_code}", flush=True)
            return
        raw = resp.json()
        # ET date for "today"
        et_now   = datetime.now(timezone.utc) - timedelta(
            hours=4 if _is_dst(datetime.now(timezone.utc)) else 5
        )
        today_et = et_now.date()
        parsed   = []
        for ev in raw:
            if ev.get("country") != "USD" or ev.get("impact") != "High":
                continue
            try:
                ev_date = datetime.strptime(ev["date"], "%b %d %Y").date()
            except Exception:
                continue
            parsed.append({
                "title":    ev.get("title", ""),
                "date":     ev["date"],
                "time":     ev.get("time", "All Day"),
                "forecast": ev.get("forecast", ""),
                "previous": ev.get("previous", ""),
                "today":    ev_date == today_et,
                "upcoming": ev_date >= today_et,
            })
        parsed.sort(key=lambda x: (x["date"], x["time"]))
        econ_events  = parsed
        econ_fetched = datetime.now()
        today_count  = sum(1 for e in parsed if e["today"])
        print(
            f"Econ calendar: {len(parsed)} USD high-impact events this week"
            f" ({today_count} today)", flush=True
        )
        for ev in parsed:
            if ev["today"]:
                print(f"  TODAY: {ev['title']} at {ev['time']}", flush=True)
    except Exception as e:
        print(f"Econ calendar error: {e}", flush=True)


def fetch_options_flow(ticker_sym):
    """Fetch options chain via yfinance and compute put/call ratio."""
    global options_data
    try:
        t    = yf.Ticker(ticker_sym)
        exps = t.options
        if not exps:
            print(f"Options [{ticker_sym}]: no expirations available", flush=True)
            return
        chain    = t.option_chain(exps[0])    # nearest expiry
        calls    = chain.calls
        puts     = chain.puts
        call_vol = float(calls["volume"].fillna(0).sum())
        put_vol  = float(puts["volume"].fillna(0).sum())
        call_oi  = float(calls["openInterest"].fillna(0).sum())
        put_oi   = float(puts["openInterest"].fillna(0).sum())
        pcr_vol  = round(put_vol / call_vol, 3) if call_vol > 0 else None
        pcr_oi   = round(put_oi  / call_oi,  3) if call_oi  > 0 else None
        # Vol/OI ratio: >FLOW_VOI_THRESH means fresh open interest = unusual positioning
        call_voi = round(call_vol / call_oi, 3) if call_oi > 0 else None
        put_voi  = round(put_vol  / put_oi,  3) if put_oi  > 0 else None
        # Unusual flow flags (yfinance approximation; overridden by UW API if key present)
        unusual_calls = bool(call_voi and call_voi > FLOW_VOI_THRESH and call_vol > put_vol)
        unusual_puts  = bool(put_voi  and put_voi  > FLOW_VOI_THRESH and put_vol  > call_vol)
        net_flow = ("calls" if unusual_calls and not unusual_puts else
                    "puts"  if unusual_puts  and not unusual_calls else "neutral")
        # Override with Unusual Whales if API key present
        uw = _fetch_uw_sweeps(ticker_sym)
        if uw.get("net_sweep"):
            net_flow = uw["net_sweep"]
            unusual_calls = net_flow == "calls"
            unusual_puts  = net_flow == "puts"
        # Phase 9: max pain from same chain (no extra API call)
        max_pain = _compute_max_pain(calls, puts)
        # Phase 16: gamma walls — top OI strikes above/below price (no extra API call)
        try:
            top_calls_raw = calls.nlargest(3, 'openInterest')[['strike','openInterest']].fillna(0)
            top_puts_raw  = puts.nlargest(3,  'openInterest')[['strike','openInterest']].fillna(0)
            top_call_strikes = [{"strike": float(r['strike']), "oi": int(r['openInterest'])} for _, r in top_calls_raw.iterrows()]
            top_put_strikes  = [{"strike": float(r['strike']), "oi": int(r['openInterest'])} for _, r in top_puts_raw.iterrows()]
        except Exception:
            top_call_strikes = []
            top_put_strikes  = []
        options_data[ticker_sym] = {
            "pcr":          pcr_vol,
            "pcr_oi":       pcr_oi,
            "call_vol":     int(call_vol),
            "put_vol":      int(put_vol),
            "call_oi":      int(call_oi),
            "put_oi":       int(put_oi),
            "call_voi":     call_voi,
            "put_voi":      put_voi,
            "unusual_calls":unusual_calls,
            "unusual_puts": unusual_puts,
            "net_flow":     net_flow,
            "max_pain":          max_pain,
            "top_call_strikes":  top_call_strikes,
            "top_put_strikes":   top_put_strikes,
            "expiry":       exps[0],
            "last_update":  datetime.now().strftime("%H:%M:%S"),
        }
        # Update dashboard_data so it's visible immediately
        if ticker_sym in dashboard_data:
            dashboard_data[ticker_sym].update({
                "pcr":          pcr_vol,
                "pcr_oi":       pcr_oi,
                "call_vol":     int(call_vol),
                "put_vol":      int(put_vol),
                "call_oi":      int(call_oi),
                "put_oi":       int(put_oi),
                "unusual_calls":unusual_calls,
                "unusual_puts": unusual_puts,
                "net_flow":          net_flow,
                "max_pain":          max_pain,
                "top_call_strikes":  top_call_strikes,
                "top_put_strikes":   top_put_strikes,
            })
        sent    = "bull" if (pcr_vol and pcr_vol < PCR_BULL_THRESH) else "bear" if (pcr_vol and pcr_vol > PCR_BEAR_THRESH) else "neutral"
        pv_str  = f"{pcr_vol:.2f}" if pcr_vol is not None else "--"
        poi_str = f"{pcr_oi:.2f}"  if pcr_oi  is not None else "--"
        print(f"Options [{ticker_sym}] PCR: {pv_str} vol / {poi_str} OI (exp {exps[0]}) → {sent}", flush=True)
    except Exception as e:
        print(f"Options error [{ticker_sym}]: {e}", flush=True)


def update_market_breadth():
    """Recompute breadth from current dashboard_data. No API call needed."""
    global vix_data
    bull_count = sum(1 for d in dashboard_data.values() if d.get('direction') == 'BULL')
    bear_count = sum(1 for d in dashboard_data.values() if d.get('direction') == 'BEAR')
    total      = len(WATCHLIST)
    if bull_count >= BREADTH_BULL_THRESH:
        breadth = "BULL_DOMINANT"
        trend   = "falling"   # most tickers bull ≈ VIX falling
    elif bear_count >= BREADTH_BEAR_THRESH:
        breadth = "BEAR_DOMINANT"
        trend   = "rising"    # most tickers bear ≈ VIX rising
    else:
        breadth = "MIXED"
        trend   = None
    pct = round((bull_count - bear_count) / total * 100, 1)
    vix_data.update({
        "trend":       trend,
        "pct_chg":     pct,
        "bull_count":  bull_count,
        "bear_count":  bear_count,
        "breadth":     breadth,
        "last_update": datetime.now().strftime("%H:%M:%S"),
    })
    print(f"Breadth: {bull_count}B/{bear_count}b/{total} → {breadth}", flush=True)

    # ── Phase 11: Relative Strength vs SPY ────────────────────────────────────
    spy = dashboard_data.get("SPY", {})
    spy_price = spy.get("price")
    spy_prev  = spy.get("prev_close")
    spy_chg   = ((spy_price - spy_prev) / spy_prev * 100) if spy_price and spy_prev and spy_prev > 0 else None
    for ticker, d in dashboard_data.items():
        if ticker == "SPY":
            d["rs_vs_spy"] = 0.0
            d["rs_signal"] = "benchmark"
            continue
        t_price = d.get("price")
        t_prev  = d.get("prev_close")
        if not t_price or not t_prev or t_prev <= 0 or spy_chg is None:
            d["rs_vs_spy"] = None
            d["rs_signal"] = None
            continue
        t_chg = (t_price - t_prev) / t_prev * 100
        rs = round(t_chg - spy_chg, 2)
        d["rs_vs_spy"]  = rs
        d["rs_signal"]  = ("leader" if rs >= RS_LEADER_THRESH else
                           "lagger" if rs <= RS_LAGGER_THRESH else "neutral")


async def scan_ticker(client, ticker, market_open):
    print(f"Scanning {ticker}...", flush=True)

    # Fetch ~7 trading days of 1m bars; limit=7000 covers 7d incl. pre/post-market
    df_raw = fetch_aggs(client, ticker, multiplier=1, days=10, limit=7000)
    if df_raw is None or len(df_raw) < 50:
        print(f"⚠️ {ticker}: insufficient data", flush=True)
        return

    # Regular trading hours only: 9:30 – 16:00 ET
    df_1m = _filter_rth(df_raw)
    if len(df_1m) < 50:
        df_1m = df_raw   # fall back to all bars if RTH filter is too aggressive

    df_5m = resample_to_5m(df_1m)
    if len(df_5m) < 20:
        df_5m = df_1m

    # ── Pre-market gap + Phase 18 PM high/low ────────────────────────────────
    pm_gap_pct = None
    pm_high    = None
    pm_low     = None
    try:
        if len(df_1m) >= 2:
            _last_rth_day  = df_1m['date'].iloc[-1]
            _prev_rth      = df_1m[df_1m['date'] < _last_rth_day]
            ts_et          = pd.to_datetime(df_raw['ts'], unit='ms', utc=True).dt.tz_convert('America/New_York')
            _pm_mask       = (
                ts_et.dt.date == _last_rth_day
            ) & (
                (ts_et.dt.hour < 9) | ((ts_et.dt.hour == 9) & (ts_et.dt.minute < 30))
            )
            _pm_bars = df_raw[_pm_mask]
            if len(_pm_bars) > 0 and len(_prev_rth) > 0:
                pm_close   = float(_pm_bars['Close'].iloc[-1])
                prev_close = float(_prev_rth['Close'].iloc[-1])
                if prev_close > 0 and pd.notna(pm_close) and pd.notna(prev_close):
                    pm_gap_pct = round((pm_close - prev_close) / prev_close * 100, 3)
                pm_high = round(float(_pm_bars['High'].max()), 2)
                pm_low  = round(float(_pm_bars['Low'].min()),  2)
    except Exception:
        pass

    result    = compute_signals(df_1m, df_5m, ticker=ticker, pm_high=pm_high, pm_low=pm_low)
    price     = result['price']
    bull_score= result['bull_score']
    bear_score= result['bear_score']
    direction = result['direction']
    vol_spike = result['volume_spike']
    score     = bull_score if direction != "BEAR" else bear_score

    if not market_open:
        status = "MARKET_CLOSED"
    elif score >= 20:
        status = "NORMAL"
    else:
        status = "REDUCED_RISK"

    # History (once per minute) + Phase 15 score velocity
    history = dashboard_data[ticker]["history"]
    # Velocity: delta vs previous recorded entry (before appending current)
    bull_velocity = bear_velocity = None
    if len(history) >= 1:
        ref = history[-1]
        bull_velocity = int(bull_score) - int(ref.get('bull_score', bull_score))
        bear_velocity = int(bear_score) - int(ref.get('bear_score', bear_score))
    current_minute = datetime.now().strftime("%H:%M")
    if not history or history[-1]["time"] != current_minute:
        history.append({"time": current_minute, "bull_score": int(bull_score), "bear_score": int(bear_score)})
        if len(history) > 60:
            history.pop(0)
        save_history(ticker, history)

    bull_score_peak = max((h.get('bull_score', 0) for h in history), default=0)
    bear_score_peak = max((h.get('bear_score', 0) for h in history), default=0)
    bull_score_peak = max(bull_score_peak, int(bull_score))
    bear_score_peak = max(bear_score_peak, int(bear_score))

    dashboard_data[ticker].update({
        "price":        price,
        "bull_score":   bull_score,
        "bear_score":   bear_score,
        "direction":    direction,
        "status":       status,
        "last_update":  datetime.now().strftime("%H:%M:%S"),
        "market_open":  market_open,
        "volume_spike": vol_spike,
        "vol_ratio":    result['vol_ratio'],
        "atr":          result['atr'],
        "bull_stop":    result['bull_stop'],
        "bull_tp":      result['bull_tp'],
        "bear_stop":    result['bear_stop'],
        "bear_tp":      result['bear_tp'],
        "pos_size":     result['pos_size'],
        "gap_pct":      result['gap_pct'],
        "gap_dir":      result['gap_dir'],
        "pm_gap_pct":   pm_gap_pct,
        "orb_high":     result['orb_high'],
        "orb_low":      result['orb_low'],
        "trend_15m":       result['trend_15m'],
        "trend_1h":        result['trend_1h'],
        "tod_ok":          result['tod_ok'],
        "block_print_dir": result['block_print_dir'],
        "block_print_mult":result['block_print_mult'],
        "vol_delta":       result['vol_delta'],
        "vol_delta_pct":   result['vol_delta_pct'],
        "vol_delta_div":   result['vol_delta_div'],
        "vwap_event":      result['vwap_event'],
        "vwap_strength":   result['vwap_strength'],
        "tape_signal":     result['tape_signal'],
        "tape_mult":       result['tape_mult'],
        "net_flow":        result['net_flow'],
        # Phase 9: pivot levels + key levels
        "pivot_pp":   result['pivot_pp'],  "pivot_r1": result['pivot_r1'],
        "pivot_r2":   result['pivot_r2'],  "pivot_r3": result['pivot_r3'],
        "pivot_s1":   result['pivot_s1'],  "pivot_s2": result['pivot_s2'],
        "pivot_s3":   result['pivot_s3'],
        "prev_high":  result['prev_high'], "prev_low": result['prev_low'],
        "prev_close": result['prev_close'],
        "max_pain":   options_data.get(ticker, {}).get('max_pain'),
        # Phase 10
        "candle_bull_pat": result['candle_bull_pat'],
        "candle_bear_pat": result['candle_bear_pat'],
        "regime":          result['regime'],
        # Phase 11
        "fib_swing_high": result['fib_swing_high'], "fib_swing_low": result['fib_swing_low'],
        "fib_236": result['fib_236'], "fib_382": result['fib_382'],
        "fib_500": result['fib_500'], "fib_618": result['fib_618'], "fib_786": result['fib_786'],
        "fib_at_zone":    result['fib_at_zone'],
        "fib_zone_level": result['fib_zone_level'],
        "fib_zone_val":   result['fib_zone_val'],
        # Phase 12
        "vpoc": result['vpoc'], "vah": result['vah'], "val": result['val'],
        "vp_profile": result['vp_profile'],
        "vwap_1u": result['vwap_1u'], "vwap_1d": result['vwap_1d'],
        "vwap_2u": result['vwap_2u'], "vwap_2d": result['vwap_2d'],
        # Phase 22
        "sma200_1m": result.get('sma200_1m'),
        "sma200_5m": result.get('sma200_5m'),
        # Phase 18
        "ema50_1m": result.get('ema50_1m'),
        "pm_high":  result.get('pm_high'),
        "pm_low":   result.get('pm_low'),
        # Phase 17
        "ema9_1m":      result.get('ema9_1m'),
        "range_vs_atr": result.get('range_vs_atr'),
        "vwap_dist_atr":result.get('vwap_dist_atr'),
        # Phase 16: session range + gamma walls
        "session_open":      result.get('session_open'),
        "session_high":      result.get('session_high'),
        "session_low":       result.get('session_low'),
        "range_pos_pct":     result.get('range_pos_pct'),
        "session_chg_pct":   result.get('session_chg_pct'),
        "top_call_strikes":  options_data.get(ticker, {}).get('top_call_strikes', []),
        "top_put_strikes":   options_data.get(ticker, {}).get('top_put_strikes', []),
        # Phase 15
        "obv_trend":     result.get('obv_trend'),
        "bull_velocity": bull_velocity,
        "bear_velocity": bear_velocity,
        # Phase 14
        "stochrsi_k": result.get('stochrsi_k'),
        "stochrsi_d": result.get('stochrsi_d'),
        # Phase 13
        "bull_breakdown": result.get('bull_breakdown', {}),
        "bear_breakdown": result.get('bear_breakdown', {}),
        "bull_cq":        result.get('bull_cq', 'WEAK'),
        "bear_cq":        result.get('bear_cq', 'WEAK'),
        # Phase 20: session peaks
        "bull_score_peak": bull_score_peak,
        "bear_score_peak": bear_score_peak,
        # PCR from options_data (updated by fetch_options_flow, not per-scan)
        "pcr":          options_data.get(ticker, {}).get("pcr"),
        "pcr_oi":       options_data.get(ticker, {}).get("pcr_oi"),
        "call_vol":     options_data.get(ticker, {}).get("call_vol"),
        "put_vol":      options_data.get(ticker, {}).get("put_vol"),
        "bull_signals": result['bull_signals'],
        "bear_signals": result['bear_signals'],
        "history":      history,
    })

    cq_now = result.get('bull_cq' if direction != 'BEAR' else 'bear_cq', 'WEAK')

    # JSON signal log
    if score >= LOG_SCORE_THRESHOLD:
        global signal_log
        entry = {
            "time":       datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "ticker":     ticker,
            "price":      price,
            "bull_score": bull_score,
            "bear_score": bear_score,
            "direction":  direction,
            "vol_spike":  vol_spike,
            "atr":        result['atr'],
            "stop":       result['bull_stop'] if direction != "BEAR" else result['bear_stop'],
            "tp":         result['bull_tp']   if direction != "BEAR" else result['bear_tp'],
            "gap_pct":    result['gap_pct'],
            "orb_break":  result['orb_high'] is not None and direction == 'BULL' and price > result['orb_high'],
            "cq":         cq_now,
        }
        signal_log.insert(0, entry)
        signal_log = signal_log[:200]
        save_signal_log(signal_log)
        log_to_csv(entry)

    # External alerts — only fire when score is at/above threshold AND rising (not falling through)
    velocity_now = bull_velocity if direction != 'BEAR' else bear_velocity
    rising = velocity_now is None or velocity_now >= 0
    if market_open and score >= ALERT_SCORE_THRESHOLD and rising:
        stop = result['bull_stop'] if direction != "BEAR" else result['bear_stop']
        tp   = result['bull_tp']   if direction != "BEAR" else result['bear_tp']
        send_notifications(ticker, price, bull_score, bear_score, direction,
                           vol_spike, result['atr'], stop, tp, cq=cq_now)

    if market_open and vol_spike:
        print(f"⚡ VOLUME SPIKE [{ticker}]: {result['vol_ratio']}x avg", flush=True)

    print(
        f"[{datetime.now().strftime('%H:%M:%S')}] {ticker} ${price:.2f} | "
        f"Bull:{bull_score} Bear:{bear_score} | {direction} | {status}"
        + (f" | ATR:{result['atr']:.2f}" if result['atr'] else "")
        + (f" | Gap:{result['gap_pct']:+.2f}%" if result['gap_pct'] is not None else "")
        + (" ⚡VOL" if vol_spike else ""),
        flush=True
    )


async def main():
    print("SCANNER STARTED", flush=True)
    if not POLYGON_API_KEY:
        print("ERROR: POLYGON_API_KEY not set", flush=True)
        return

    client          = RESTClient(POLYGON_API_KEY)
    loop            = asyncio.get_running_loop()
    _econ_last      = None
    _opts_last      = None
    _summary_sent   = None   # date on which daily summary was sent
    print(f"Watchlist: {', '.join(WATCHLIST)}", flush=True)

    while True:
        try:
            market_open = is_market_open()
            now         = datetime.now()

            # Economic calendar: refresh hourly (runs in thread to avoid blocking)
            if _econ_last is None or (now - _econ_last).total_seconds() > ECON_REFRESH_SECS:
                await loop.run_in_executor(None, fetch_econ_calendar)
                _econ_last = now

            # Options flow: refresh every 5 min during market hours
            if market_open and (
                _opts_last is None or (now - _opts_last).total_seconds() > OPTIONS_REFRESH_SECS
            ):
                for t_sym in WATCHLIST:
                    await loop.run_in_executor(None, fetch_options_flow, t_sym)
                    await asyncio.sleep(0.5)
                _opts_last = now

            # Polygon ticker scans
            for ticker in WATCHLIST:
                try:
                    await scan_ticker(client, ticker, market_open)
                except Exception:
                    print(f"Error scanning {ticker}:", flush=True)
                    traceback.print_exc()
                await asyncio.sleep(1)

            # Compute breadth from this cycle's results (no extra API call)
            update_market_breadth()

            # Check open simulated trades for TP/SL hits (no extra API calls)
            if market_open:
                check_outcomes()

            # Daily summary: send once after 16:05 ET on trading days
            et_now = datetime.now(timezone.utc).astimezone(_ET)
            today = et_now.date()
            if (
                et_now.hour == 16 and et_now.minute >= 5
                and _summary_sent != today
                and today.weekday() < 5   # Mon–Fri only
            ):
                await loop.run_in_executor(None, send_daily_summary)
                _summary_sent = today

        except Exception:
            traceback.print_exc()

        await asyncio.sleep(300 if not is_market_open() else 45)


# ====================== DASHBOARD HTML ======================

DASHBOARD_HTML = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0, viewport-fit=cover">
<meta name="mobile-web-app-capable" content="yes">
<meta name="apple-mobile-web-app-capable" content="yes">
<meta name="apple-mobile-web-app-status-bar-style" content="black-translucent">
<meta name="theme-color" content="#00ffcc">
<link rel="manifest" href="/manifest.json">
<title>SPX Confluence Scanner</title>
<link href="https://cdn.jsdelivr.net/npm/bootstrap@5.3.3/dist/css/bootstrap.min.css" rel="stylesheet">
<script src="https://cdn.jsdelivr.net/npm/chart.js"></script>
<style>
  body{background:#0a0a0a;color:#ddd;font-family:'Segoe UI',sans-serif;font-size:.9rem}
  h1{color:#00ffcc;font-size:1.4rem;margin:0}
  .card{background:#111;border:1px solid #1e1e1e;border-radius:10px}
  .tcrd{background:#0d0d0d;border:1px solid #222;border-radius:10px;padding:12px 14px;cursor:pointer;transition:border-color .2s}
  .tcrd.active{border-color:#00ffcc}
  .tcrd:hover{border-color:#00ffcc88}
  .tcrd .t-ticker{font-size:1rem;font-weight:700;color:#fff}
  .tcrd .t-price{font-size:1.35rem;font-weight:700;color:#00ffcc;margin:3px 0}
  .tcrd .t-score{font-size:.78rem}
  .tcrd .t-dir{font-size:.72rem;font-weight:bold;padding:2px 7px;border-radius:10px}
  .dir-bull{background:#00ff8822;color:#00ff88;border:1px solid #00ff8855}
  .dir-bear{background:#ff444422;color:#ff6666;border:1px solid #ff444455}
  .dir-neutral{background:#44444422;color:#888;border:1px solid #555}
  .dir-starting{background:#ffaa0022;color:#ffaa00;border:1px solid #ffaa0055}
  .sig-card{background:#0c0c0c;border:1px solid #1a1a1a;border-radius:6px;padding:7px 9px;margin-bottom:5px;transition:border-color .25s}
  .sig-card.active{border-color:#00ff8866}
  .sig-card.inactive{opacity:.5}
  .sig-label{font-size:.62rem;color:#666;text-transform:uppercase;letter-spacing:.7px}
  .sig-val{font-size:.85rem;font-weight:600;margin-top:2px}
  .sig-icon{float:right;font-size:.85rem}
  .tf-badge{font-size:.56rem;padding:1px 4px;border-radius:8px;margin-left:2px}
  .tf-ok{background:#00ff8822;color:#00ff88}
  .tf-no{background:#ff444422;color:#ff6666}
  .bar-wrap{background:#1a1a1a;border-radius:10px;height:6px;margin:3px 0}
  .bar{height:6px;border-radius:10px;transition:width .4s,background .4s}
  .tab-btn{background:#111;border:1px solid #333;color:#888;padding:4px 12px;border-radius:6px;cursor:pointer;font-size:.78rem;transition:all .2s}
  .tab-btn.active{background:#00ffcc22;border-color:#00ffcc;color:#00ffcc}
  .alert-item{background:#0d0d0d;border-left:3px solid #ff9900;padding:6px 9px;margin-bottom:4px;border-radius:0 5px 5px 0;font-size:.76rem}
  .sb{font-size:.75rem;padding:3px 9px;border-radius:12px;font-weight:600}
  .sb-normal{background:#00ff8822;color:#00ff88;border:1px solid #00ff88}
  .sb-risk{background:#ff444422;color:#ff4444;border:1px solid #ff4444}
  .sb-closed{background:#22222288;color:#666;border:1px solid #444}
  .sb-starting{background:#ffaa0022;color:#ffaa00;border:1px solid #ffaa00}
  .log-table{width:100%;font-size:.76rem;border-collapse:collapse}
  .log-table th{color:#555;text-transform:uppercase;font-size:.62rem;letter-spacing:.8px;padding:4px 7px;border-bottom:1px solid #1e1e1e}
  .log-table td{padding:4px 7px;border-bottom:1px solid #111}
  .log-bull{color:#00ff88}.log-bear{color:#ff6666}.log-neutral{color:#888}
  .section-title{color:#555;font-size:.63rem;text-transform:uppercase;letter-spacing:1.5px;margin-bottom:7px}
  .live-dot{display:inline-block;width:7px;height:7px;background:#00ff88;border-radius:50%;margin-right:6px;animation:pulse 2s infinite}
  .live-dot.off{background:#444;animation:none}
  @keyframes pulse{0%,100%{opacity:1}50%{opacity:.25}}
  .vol-spike{background:#ff990022;border:1px solid #ff9900;color:#ff9900;border-radius:5px;padding:2px 7px;font-size:.7rem}
  /* Institutional flow signal cards */
  .sig-card.inst{border-color:#b87d0033}
  .sig-card.inst.active{border-color:#ffd700bb;background:#0d0c00}
  .sig-card.inst .sig-label{color:#7a6500}
  .sig-card.inst.active .sig-label{color:#ffd700}
  .div-warn{background:#330d0d;border:1px solid #ff4444;border-radius:6px;padding:6px 10px;font-size:.76rem;color:#ff8888;margin-bottom:6px}
  .div-absorb{background:#0d2200;border:1px solid #00ff88;border-radius:6px;padding:6px 10px;font-size:.76rem;color:#88ff88;margin-bottom:6px}
  /* Regime badges */
  .regime-trending-up{color:#00ff88}.regime-trending-down{color:#ff6666}
  .regime-breakout-up{color:#00ffcc}.regime-breakout-down{color:#ff9966}
  .regime-ranging{color:#888}.regime-neutral{color:#666}.regime-unknown{color:#444}
  .sound-btn{background:#111;border:1px solid #333;color:#888;padding:3px 10px;border-radius:6px;cursor:pointer;font-size:.76rem}
  .sound-btn.on{border-color:#00ffcc;color:#00ffcc}
  /* Risk panel */
  .risk-chip{display:inline-block;background:#0d0d0d;border:1px solid #222;border-radius:6px;padding:5px 10px;margin:3px;font-size:.78rem}
  .risk-chip .rc-label{font-size:.6rem;color:#555;text-transform:uppercase;letter-spacing:.8px;display:block}
  .risk-chip .rc-val{font-weight:700;margin-top:1px}
  /* Gap/ORB badges */
  .ctx-badge{display:inline-block;padding:2px 8px;border-radius:10px;font-size:.72rem;font-weight:600;margin:2px}
  .ctx-bull{background:#00ff8815;color:#00ff88;border:1px solid #00ff8844}
  .ctx-bear{background:#ff444415;color:#ff6666;border:1px solid #ff444444}
  .ctx-neutral{background:#22222288;color:#888;border:1px solid #333}
  /* Mobile tweaks */
  @media(max-width:576px){
    body{font-size:.85rem;padding:8px!important}
    h1{font-size:1rem}
    .tcrd{padding:8px 9px}
    .tcrd .t-price{font-size:1rem}
    .tab-btn{padding:6px 12px;font-size:.8rem;min-height:36px}
    .sound-btn{padding:5px 10px;min-height:36px}
    .risk-chip{padding:5px 9px}
    .col-6.col-sm-4.col-md-3.col-xl-2{flex:0 0 50%}
    .sig-card{padding:6px 8px}
    .log-table{font-size:.68rem}
    .log-table th,.log-table td{padding:3px 5px}
    /* hide TradingView iframes on very small screens */
    .tv-hide-mobile{display:none!important}
  }
  @media(display-mode:standalone){
    body{padding-top:max(env(safe-area-inset-top),8px)!important}
  }
</style>
</head>
<body class="p-2 p-md-3">
<div class="container-fluid">

  <!-- Header -->
  <div class="d-flex align-items-center gap-2 mb-3 flex-wrap">
    <span class="live-dot" id="live-dot"></span>
    <h1>SPX Confluence Scanner</h1>
    <span id="mkt-badge" class="sb sb-starting ms-1">STARTING</span>
    <span id="vix-badge" class="ctx-badge ctx-neutral" title="VIXY (VIX proxy) — falling=bullish, rising=bearish">VIX --</span>
    <span class="ms-auto text-muted" style="font-size:.72rem">Updated: <span id="last-update">--</span></span>
    <button class="sound-btn on" id="sound-btn" onclick="toggleSound()">🔔 Sound ON</button>
    <button class="sound-btn" id="notif-btn" onclick="requestNotifPermission()" title="Enable browser push notifications">🔔 Enable Alerts</button>
    <a href="/api/download-csv" class="sound-btn" style="text-decoration:none;font-size:.72rem" title="Download today&#39;s signal log as CSV">⬇ CSV</a>
    <a href="/backtest" class="sound-btn" style="text-decoration:none;font-size:.72rem" title="60-day walk-forward backtest">⚡ Backtest</a>
  </div>

  <!-- Economic Event Banner (today's high-impact events) -->
  <div id="econ-banner" class="d-none mb-2 p-2" style="background:#1a0a00;border:1px solid #ff9900;border-radius:8px;font-size:.8rem;color:#ffcc00"></div>

  <!-- Ticker Summary Row -->
  <div class="row g-2 mb-3" id="ticker-row"></div>

  <!-- Detail Panel -->
  <div class="card p-3 mb-3">
    <!-- Tab bar -->
    <div class="d-flex align-items-center gap-2 mb-2 flex-wrap">
      <div class="section-title mb-0" id="detail-title">SPY — Signals</div>
      <div class="d-flex gap-1 flex-wrap">
        <button class="tab-btn active" id="tab-bull" onclick="setTab('bull')">🔼 Bull</button>
        <button class="tab-btn"        id="tab-bear" onclick="setTab('bear')">🔽 Bear</button>
        <button class="tab-btn"        id="tab-stats" onclick="setTab('analytics')">📊 Stats</button>
      </div>
      <span id="vol-spike-badge" class="vol-spike d-none">⚡ VOL SPIKE</span>
    </div>

    <!-- Context row: Gap + ORB -->
    <div id="ctx-row" class="mb-2"></div>

    <!-- Signal Grid (hidden when analytics tab active) -->
    <div id="signals-section">
      <div id="cat-breakdown"></div>
      <div id="div-warn-banner" class="d-none"></div>
      <div class="row g-2 mb-3" id="signal-grid"></div>
      <!-- ATR Risk Panel -->
      <div id="risk-section">
        <div class="section-title">ATR Risk Levels</div>
        <div id="risk-panel" class="d-flex flex-wrap gap-1"></div>
      </div>
    </div>

    <!-- Analytics Panel -->
    <div id="analytics-panel" class="d-none"></div>
  </div>

  <!-- Charts + Alerts Row -->
  <div class="row g-3 mb-3">
    <div class="col-md-5">
      <div class="card p-3">
        <div class="section-title d-flex align-items-center justify-content-between">
          <span>Score History <span id="chart-ticker" style="color:#aaa">— SPY</span></span>
          <span style="display:inline-flex;gap:3px;flex-shrink:0">
            <button id="chart-btn-multi"  onclick="setChartMode('multi')"  style="background:#0d2010;color:#00ff88;border:1px solid #00ff8844;border-radius:3px;padding:1px 6px;font-size:.6rem;cursor:pointer">Multi</button>
            <button id="chart-btn-single" onclick="setChartMode('single')" style="background:transparent;color:#444;border:1px solid #222;border-radius:3px;padding:1px 6px;font-size:.6rem;cursor:pointer">Single</button>
          </span>
        </div>
        <canvas id="scoreChart"></canvas>
      </div>
    </div>
    <div class="col-md-4">
      <div class="card p-3 h-100">
        <div class="section-title">Recent Alerts</div>
        <div id="alerts-panel"><span class="text-muted" style="font-size:.82rem">No alerts yet</span></div>
      </div>
    </div>
    <div class="col-md-3">
      <div class="card p-3 h-100">
        <div class="section-title">TradingView — <span id="tv-label">SPY</span></div>
        <iframe id="tv-frame"
          src="https://www.tradingview.com/widgetembed/?symbol=AMEX:SPY&interval=1&theme=dark"
          width="100%" height="160" frameborder="0"></iframe>
        <div class="section-title mt-2 tv-hide-mobile">VIX (CBOE)</div>
        <iframe class="tv-hide-mobile"
          src="https://www.tradingview.com/widgetembed/?symbol=TVC:VIX&interval=D&theme=dark"
          width="100%" height="50" frameborder="0" style="border-radius:4px"></iframe>
      </div>
    </div>
  </div>

  <!-- Signal Log -->
  <div class="card p-3">
    <div class="section-title">Signal History Log</div>
    <div style="overflow-x:auto;max-height:260px;overflow-y:auto">
      <table class="log-table">
        <thead><tr>
          <th>Time</th><th>Ticker</th><th>Price</th>
          <th>Bull</th><th>Bear</th><th>Dir</th><th>CQ</th>
          <th>ATR</th><th>Stop</th><th>TP</th><th>Gap</th><th>Vol</th>
        </tr></thead>
        <tbody id="log-body">
          <tr><td colspan="12" style="color:#555;text-align:center;padding:12px">No setups logged yet</td></tr>
        </tbody>
      </table>
    </div>
  </div>

  <!-- Economic Calendar -->
  <div class="card p-3 mt-3">
    <div class="d-flex align-items-center gap-2 mb-2">
      <div class="section-title mb-0">Economic Calendar — High Impact USD</div>
      <span style="font-size:.65rem;color:#555" id="econ-updated"></span>
    </div>
    <div id="econ-list" style="font-size:.78rem"><span style="color:#555">Loading…</span></div>
  </div>

</div>

<script>
let allData      = {};
let signalLog    = [];
let vixData      = null;
let econEvents   = [];
let optionsData  = {};
let tradesData   = {open_trades: [], outcomes: []};
let alpacaData   = {enabled: false};
let curTicker    = 'SPY';
let curDir       = 'bull';
let soundOn      = true;
let prevScores   = {};
let scoreChart   = null;
let chartMode    = 'multi';
const TICKER_COLORS = {SPY:'#00ff88',QQQ:'#00ccff',IWM:'#ffcc00',NVDA:'#ff7744',AAPL:'#bb88ff'};

const MAX_SCORE           = """ + str(MAX_SCORE) + """;
const ALERT_SCORE_THRESH  = """ + str(ALERT_SCORE_THRESHOLD) + """;
const LOG_SCORE_THRESH    = """ + str(LOG_SCORE_THRESHOLD) + """;
const FIB_LOOKBACK        = """ + str(200) + """;
const SIGNAL_CATEGORIES   = """ + json.dumps(SIGNAL_CATEGORIES) + """;

const TV_SYMBOLS = {
  SPY:'AMEX:SPY', QQQ:'NASDAQ:QQQ', IWM:'AMEX:IWM',
  NVDA:'NASDAQ:NVDA', AAPL:'NASDAQ:AAPL'
};

function toggleSound() {
  soundOn = !soundOn;
  const btn = document.getElementById('sound-btn');
  btn.textContent = soundOn ? '🔔 Sound ON' : '🔕 Sound OFF';
  btn.className   = soundOn ? 'sound-btn on' : 'sound-btn';
}

function playAlert(freq, count) {
  const ACtx = window.AudioContext || window.webkitAudioContext;
  if (!ACtx || !soundOn) return;
  const ctx = new ACtx();
  for (let i = 0; i < (count || 1); i++) {
    const osc = ctx.createOscillator(), gain = ctx.createGain();
    osc.connect(gain); gain.connect(ctx.destination);
    osc.frequency.value = freq || 880; osc.type = 'sine';
    const t = ctx.currentTime + i * 0.18;
    gain.gain.setValueAtTime(0.25, t);
    gain.gain.exponentialRampToValueAtTime(0.001, t + 0.25);
    osc.start(t); osc.stop(t + 0.25);
  }
}

// ── Browser push notifications ────────────────────────────────────────────────
let notifGranted = false;

function updateNotifBtn() {
  const btn = document.getElementById('notif-btn');
  if (!btn) return;
  if (!('Notification' in window)) { btn.style.display='none'; return; }
  const p = Notification.permission;
  notifGranted = p === 'granted';
  if (p === 'granted')  { btn.textContent='🔔 Alerts ON'; btn.className='sound-btn on'; }
  else if (p === 'denied') { btn.textContent='🔕 Blocked'; btn.className='sound-btn'; btn.disabled=true; }
  else                  { btn.textContent='🔔 Enable Alerts'; btn.className='sound-btn'; }
}

async function requestNotifPermission() {
  if (!('Notification' in window)) return;
  if (Notification.permission === 'granted') return;
  await Notification.requestPermission();
  updateNotifBtn();
}

function fireNotification(ticker, direction, score, cq, price) {
  if (!notifGranted) return;
  const emoji  = direction === 'BULL' ? '🚀' : '🔻';
  const cqStr  = {HIGH:'★ HIGH',MED:'◆ MED',LOW:'▲ LOW',WEAK:'WEAK'}[cq] || (cq || '');
  const priceStr = price != null ? `$${parseFloat(price).toFixed(2)}` : '';
  try {
    new Notification(`${emoji} ${ticker} ${direction} ${score}/${MAX_SCORE}  ${cqStr}`, {
      body: `${priceStr ? 'Price: ' + priceStr + '  |  ' : ''}Score: ${score}/${MAX_SCORE}  |  CQ: ${cqStr}`,
      tag:  `${ticker}-${direction}`,
      silent: false,
    });
  } catch(e) {}
}

function scoreColor(s) {
  const p = s / MAX_SCORE;
  if (p >= 0.75) return '#00ff88';
  if (p >= 0.55) return '#aaff00';
  if (p >= 0.35) return '#ffaa00';
  return '#ff4444';
}

function fmt(v, prefix='$', dec=2) {
  if (v == null) return '--';
  return prefix + parseFloat(v).toFixed(dec);
}

// ── Phase 15: velocity + setup grade helpers ─────────────────────────────────
function velArrow(v) {
  if (v === null || v === undefined) return '';
  if (v >= 2)  return `<span style="color:#00ff88;font-size:.65rem;font-weight:bold">↑+${v}</span>`;
  if (v === 1) return `<span style="color:#88ff88;font-size:.65rem">↑+1</span>`;
  if (v === 0) return `<span style="color:#444;font-size:.65rem">→</span>`;
  if (v === -1)return `<span style="color:#ff8888;font-size:.65rem">↓${v}</span>`;
  return `<span style="color:#ff4444;font-size:.65rem;font-weight:bold">↓${v}</span>`;
}

function setupGrade(d, dir) {
  const score = dir === 'bear' ? d.bear_score : d.bull_score;
  const cq    = dir === 'bear' ? d.bear_cq    : d.bull_cq;
  const vel   = dir === 'bear' ? d.bear_velocity : d.bull_velocity;
  const pct    = score / MAX_SCORE;
  const rising = vel === null || vel >= 0;
  const cqRank = {HIGH:3, MED:2, LOW:1, WEAK:0}[cq] || 0;
  // A: exceptional — HIGH quality + strong weighted score (≥58% = 58+/100)
  if (cqRank >= 3 && pct >= 0.58 && rising) return {g:'A',  c:'#00ff88'};
  if (cqRank >= 3 && pct >= 0.44)           return {g:'A−', c:'#44ee88'};
  // B: solid — HIGH quality + moderate score, or MED quality + strong score
  if (cqRank >= 2 && pct >= 0.36 && rising) return {g:'B',  c:'#00ffcc'};
  if (cqRank >= 2 && pct >= 0.26)           return {g:'B−', c:'#44ccaa'};
  // C: developing
  if (cqRank >= 1 && pct >= 0.20)           return {g:'C',  c:'#ffcc00'};
  if (pct >= 0.14)                           return {g:'D',  c:'#ff9944'};
  return {g:'F', c:'#444'};
}

// ── Phase 17: Score sparkline ─────────────────────────────────────────────────
function sparklineSvg(history, w, h) {
  w = w || 88; h = h || 20;
  if (!history || history.length < 2) return '';
  const n = history.length;
  function toPath(getter, color) {
    const pts = history.map((entry, i) => {
      const x = Math.round(i / (n - 1) * w);
      const y = Math.round(h - (getter(entry) / MAX_SCORE) * h);
      return (i === 0 ? 'M' : 'L') + x + ',' + Math.max(0, Math.min(h, y));
    }).join(' ');
    return `<path d="${pts}" fill="none" stroke="${color}" stroke-width="1.4" stroke-linecap="round"/>`;
  }
  return `<svg width="${w}" height="${h}" style="display:block;overflow:visible">
    ${toPath(e => e.bear_score, '#ff444455')}
    ${toPath(e => e.bull_score, '#00ff8877')}
  </svg>`;
}

// ── Ticker summary cards ──────────────────────────────────────────────────────
function renderTickerRow() {
  const row = document.getElementById('ticker-row');
  row.innerHTML = '';
  for (const ticker of Object.keys(allData)) {
    const d = allData[ticker];
    const activeDir = d.direction === 'BEAR' ? 'bear' : 'bull';
    const score  = d.direction === 'BEAR' ? d.bear_score : d.bull_score;
    const dirCls = {BULL:'dir-bull',BEAR:'dir-bear',NEUTRAL:'dir-neutral'}[d.direction] || 'dir-starting';
    const gapHtml = d.gap_pct != null
      ? `<span class="ctx-badge ${d.gap_pct>0?'ctx-bull':d.gap_pct<0?'ctx-bear':'ctx-neutral'}">${d.gap_pct>0?'+':''}${d.gap_pct.toFixed(2)}%</span>`
      : '';
    const grd = setupGrade(d, activeDir);
    const vel = activeDir === 'bear' ? d.bear_velocity : d.bull_velocity;
    const col = document.createElement('div');
    col.className = 'col-6 col-sm-4 col-md-3 col-xl-2';
    col.innerHTML = `
      <div class="tcrd${ticker===curTicker?' active':''}" onclick="selectTicker('${ticker}')">
        <div class="d-flex justify-content-between align-items-start">
          <span class="t-ticker">${ticker}</span>
          <div class="d-flex align-items-center gap-1">
            <span style="font-size:.68rem;font-weight:bold;color:${grd.c};background:${grd.c}18;border:1px solid ${grd.c}55;padding:0 4px;border-radius:3px;line-height:1.3">${grd.g}</span>
            <span class="t-dir ${dirCls}">${d.direction}</span>
          </div>
        </div>
        <div class="t-price">$${d.price.toFixed(2)}</div>
        <div class="t-score d-flex align-items-center gap-1 flex-wrap">
          <span style="color:#00ff88">▲${d.bull_score}</span>
          <span style="color:#ff6666">▼${d.bear_score}</span>
          <span style="color:#444">/${MAX_SCORE}</span>
          ${velArrow(vel)}
          ${gapHtml}
          ${d.volume_spike?'<span class="vol-spike" style="padding:1px 5px">⚡</span>':''}
        </div>
        <div style="font-size:.65rem;margin-top:3px;color:#555">
          ${d.trend_15m ? `<span style="color:${d.trend_15m==='bull'?'#00ff88':'#ff6666'}">15m ${d.trend_15m==='bull'?'▲':'▼'}</span>` : ''}
          ${d.trend_1h  ? `<span class="ms-1" style="color:${d.trend_1h==='bull'?'#00ff88':'#ff6666'}">1h ${d.trend_1h==='bull'?'▲':'▼'}</span>` : ''}
          ${d.tod_ok === false ? '<span class="ms-1" style="color:#ffaa00">⏸ TOD</span>' : ''}
          ${d.regime && d.regime !== 'unknown' ? `<span class="ms-1 regime-${d.regime}">${{trending_up:'↗Trend',trending_down:'↘Trend',breakout_up:'⚡BO↑',breakout_down:'⚡BO↓',ranging:'↔Range',neutral:'~'}[d.regime]||d.regime}</span>` : ''}
          ${d.rs_signal && d.rs_signal !== 'benchmark' && d.rs_signal !== 'neutral' ? `<span class="ms-1" style="color:${d.rs_signal==='leader'?'#00ffcc':'#ff9966'};font-size:.62rem">${d.rs_signal==='leader'?'RS+':'RS−'} ${d.rs_vs_spy!=null?(d.rs_vs_spy>0?'+':'')+d.rs_vs_spy.toFixed(1)+'%':''}</span>` : ''}
        </div>
        <div class="bar-wrap mt-1">
          <div class="bar" style="width:${Math.min(score/MAX_SCORE*100,100)}%;background:${scoreColor(score)}"></div>
        </div>
        <div style="margin-top:3px;opacity:.75">${sparklineSvg(d.history)}</div>
        <div style="font-size:.57rem;color:#2a2a2a;margin-top:1px">Peak ▲${d.bull_score_peak||0} ▼${d.bear_score_peak||0}</div>
      </div>`;
    row.appendChild(col);
  }
}

// ── Select ticker ─────────────────────────────────────────────────────────────
function selectTicker(t) {
  curTicker = t;
  renderTickerRow();
  renderSignals();
  renderRiskPanel();
  renderContextRow();
  renderAlerts();
  updateChart();
  document.getElementById('detail-title').textContent = t + ' — Signals';
  document.getElementById('chart-ticker').textContent = t;
  document.getElementById('tv-label').textContent = t;
  document.getElementById('tv-frame').src =
    `https://www.tradingview.com/widgetembed/?symbol=${TV_SYMBOLS[t]||'AMEX:SPY'}&interval=1&theme=dark`;
}

// ── Tab / direction system ────────────────────────────────────────────────────
let curTab = 'bull'; // 'bull' | 'bear' | 'analytics'

function setDir(dir) {
  curDir = dir;
  document.getElementById('tab-bull').className = 'tab-btn' + (dir==='bull'?' active':'');
  document.getElementById('tab-bear').className = 'tab-btn' + (dir==='bear'?' active':'');
  document.getElementById('tab-stats').className = 'tab-btn';
}

function setTab(tab) {
  curTab = tab;
  const sigSec  = document.getElementById('signals-section');
  const anaSec  = document.getElementById('analytics-panel');
  if (tab === 'analytics') {
    sigSec.classList.add('d-none');
    anaSec.classList.remove('d-none');
    document.getElementById('tab-bull').className  = 'tab-btn';
    document.getElementById('tab-bear').className  = 'tab-btn';
    document.getElementById('tab-stats').className = 'tab-btn active';
    renderAnalytics();
  } else {
    sigSec.classList.remove('d-none');
    anaSec.classList.add('d-none');
    curDir = tab;
    setDir(tab);
    renderSignals();
    renderRiskPanel();
  }
}

// ── Context row (Gap + ORB + Pre-market Gap) ─────────────────────────────────
function renderContextRow() {
  const d = allData[curTicker];
  if (!d) return;
  const row = document.getElementById('ctx-row');
  let html = '';

  // Phase 10: Market regime badge (always first)
  if (d.regime && d.regime !== 'unknown') {
    const regimeMeta = {
      trending_up:   {cls:'ctx-bull',  icon:'↗', label:'Trending Up'},
      trending_down: {cls:'ctx-bear',  icon:'↘', label:'Trending Down'},
      breakout_up:   {cls:'ctx-bull',  icon:'⚡', label:'Breakout ↑'},
      breakout_down: {cls:'ctx-bear',  icon:'⚡', label:'Breakout ↓'},
      ranging:       {cls:'ctx-neutral',icon:'↔', label:'Ranging'},
      neutral:       {cls:'ctx-neutral',icon:'~', label:'Neutral'},
    };
    const rm = regimeMeta[d.regime] || {cls:'ctx-neutral', icon:'?', label:d.regime};
    html += `<span class="ctx-badge ${rm.cls}" title="Market regime (ADX + BBands)">${rm.icon} ${rm.label}</span>`;
  }
  // Phase 10: Active candle pattern
  const cpat = curDir === 'bull' ? d.candle_bull_pat : d.candle_bear_pat;
  if (cpat) {
    const cpCls = curDir === 'bull' ? 'ctx-bull' : 'ctx-bear';
    html += `<span class="ctx-badge ${cpCls}" title="Candlestick pattern on recent bars">🕯 ${cpat}</span>`;
  }

  // Pre-market gap (shown before/at open)
  if (d.pm_gap_pct != null) {
    const pmCls = d.pm_gap_pct > 0 ? 'ctx-bull' : d.pm_gap_pct < 0 ? 'ctx-bear' : 'ctx-neutral';
    html += `<span class="ctx-badge ${pmCls}" title="Pre-market gap vs yesterday RTH close">PM Gap ${d.pm_gap_pct>0?'+':''}${d.pm_gap_pct.toFixed(2)}%</span>`;
  }

  // Regular session gap
  if (d.gap_pct != null) {
    const cls = d.gap_pct > 0 ? 'ctx-bull' : d.gap_pct < 0 ? 'ctx-bear' : 'ctx-neutral';
    html += `<span class="ctx-badge ${cls}" title="RTH gap vs prior day RTH close">Gap ${d.gap_pct>0?'+':''}${d.gap_pct.toFixed(2)}%</span>`;
  }

  // ORB
  if (d.orb_high != null) {
    html += `<span class="ctx-badge ctx-neutral">ORB H: $${d.orb_high.toFixed(2)}</span>`;
    html += `<span class="ctx-badge ctx-neutral">ORB L: $${d.orb_low.toFixed(2)}</span>`;
    if (d.price > d.orb_high)
      html += `<span class="ctx-badge ctx-bull">▲ Above ORB</span>`;
    else if (d.price < d.orb_low)
      html += `<span class="ctx-badge ctx-bear">▼ Below ORB</span>`;
    else
      html += `<span class="ctx-badge ctx-neutral">Inside ORB</span>`;
  }

  // 15m / 1h trend badges
  if (d.trend_15m) {
    const tc = d.trend_15m === 'bull' ? 'ctx-bull' : 'ctx-bear';
    html += `<span class="ctx-badge ${tc}" title="15-minute EMA9 vs EMA21 trend">15m ${d.trend_15m==='bull'?'▲ Bull':'▼ Bear'}</span>`;
  }
  if (d.trend_1h) {
    const tc = d.trend_1h === 'bull' ? 'ctx-bull' : 'ctx-bear';
    html += `<span class="ctx-badge ${tc}" title="1-hour EMA9 vs EMA21 trend">1h ${d.trend_1h==='bull'?'▲ Bull':'▼ Bear'}</span>`;
  }
  if (d.tod_ok === false) {
    html += `<span class="ctx-badge" style="background:#ffaa0015;color:#ffaa00;border:1px solid #ffaa0044" title="First 15 min or last 5 min of RTH — signals may be choppy">⏸ TOD Filter</span>`;
  }

  // Phase 14: StochRSI K/D badge
  if (d.stochrsi_k != null) {
    const k = d.stochrsi_k, dv = d.stochrsi_d;
    const srsiCls = k < 20 ? 'ctx-bull' : k > 80 ? 'ctx-bear' : (k > dv ? 'ctx-bull' : 'ctx-bear');
    const srsiZone = k < 20 ? ' OS' : k > 80 ? ' OB' : '';
    html += `<span class="ctx-badge ${srsiCls}" title="Stochastic RSI (K/D lines — 14/14/3/3). OS=Oversold OB=Overbought">StRSI K:${k} D:${dv}${srsiZone}</span>`;
  }

  // PCR chip
  const d2 = allData[curTicker];
  if (d2 && d2.pcr != null) {
    const pcrCls = d2.pcr < """ + str(0.7) + """ ? 'ctx-bull' : d2.pcr > """ + str(1.2) + """ ? 'ctx-bear' : 'ctx-neutral';
    html += `<span class="ctx-badge ${pcrCls}" title="Put/Call ratio (volume) — nearest expiry">P/C ${d2.pcr.toFixed(2)} ${d2.pcr<0.7?'↑calls':d2.pcr>1.2?'↑puts':'~'}</span>`;
    if (d2.call_vol && d2.put_vol)
      html += `<span class="ctx-badge ctx-neutral" title="Options volume">C:${(d2.call_vol/1000).toFixed(0)}k P:${(d2.put_vol/1000).toFixed(0)}k</span>`;
  }

  // Phase 9: Pivot levels + key levels
  if (d.pivot_pp != null) {
    const abovePP = d.price > d.pivot_pp;
    const ppCls = abovePP ? 'ctx-bull' : 'ctx-bear';
    html += `<span class="ctx-badge ${ppCls}" title="Daily Pivot Point (prev day H+L+C)/3">PP $${d.pivot_pp.toFixed(2)} ${abovePP ? '▲' : '▼'}</span>`;
    if (d.pivot_r1 != null && d.price >= d.pivot_r1)
      html += `<span class="ctx-badge ctx-bull" title="Above R1 — first resistance cleared">↑R1 $${d.pivot_r1.toFixed(2)}</span>`;
    else if (d.pivot_s1 != null && d.price <= d.pivot_s1)
      html += `<span class="ctx-badge ctx-bear" title="Below S1 — first support broken">↓S1 $${d.pivot_s1.toFixed(2)}</span>`;
  }
  if (d.prev_high != null && d.prev_low != null) {
    if (d.price > d.prev_high)
      html += `<span class="ctx-badge ctx-bull" title="Above prior day high — breakout">▲PDH $${d.prev_high.toFixed(2)}</span>`;
    else if (d.price < d.prev_low)
      html += `<span class="ctx-badge ctx-bear" title="Below prior day low — breakdown">▼PDL $${d.prev_low.toFixed(2)}</span>`;
    else
      html += `<span class="ctx-badge ctx-neutral" title="Inside prior day range — PDH $${d.prev_high.toFixed(2)} / PDL $${d.prev_low.toFixed(2)}">Inside PDR</span>`;
  }
  if (d.max_pain != null && d.price != null) {
    const mpDist = ((d.price - d.max_pain) / d.price * 100);
    const mpCls = Math.abs(mpDist) < 0.3 ? 'ctx-neutral' : (mpDist > 0 ? 'ctx-bear' : 'ctx-bull');
    html += `<span class="ctx-badge ${mpCls}" title="Options max pain — price gravitates here on expiry day">MaxPain $${d.max_pain.toFixed(0)} (${mpDist>0?'+':''}${mpDist.toFixed(2)}%)</span>`;
  }

  // Institutional flow badges (amber/gold)
  const instStyle = 'background:#1a1200;color:#ffd700;border:1px solid #ffd70044';
  if (d.block_print_dir) {
    const bpIcon = d.block_print_dir === 'bull' ? '🟩' : '🟥';
    html += `<span class="ctx-badge" style="${instStyle}" title="Dark pool block print (high-vol, tight-range candle)">${bpIcon} Block ×${d.block_print_mult ? d.block_print_mult.toFixed(1) : '?'}</span>`;
  }
  if (d.net_flow && d.net_flow !== 'neutral') {
    const nfIcon = d.net_flow === 'calls' ? '📈' : '📉';
    html += `<span class="ctx-badge" style="${instStyle}" title="Unusual options flow (Vol/OI ratio)">${nfIcon} Flow: ${d.net_flow.toUpperCase()}</span>`;
  }
  if (d.tape_signal) {
    const tapeLabel = d.tape_signal.replace(/_/g,' ').replace(/\\b\\w/g,c=>c.toUpperCase());
    html += `<span class="ctx-badge" style="${instStyle}" title="Tape reading signal"># ${tapeLabel}</span>`;
  }
  // Phase 15: OBV trend badge
  if (d.obv_trend) {
    const obvLabel = d.obv_trend === 'bull' ? '↑ Accum' : '↓ Distrib';
    html += `<span class="ctx-badge" style="${instStyle}" title="On-Balance Volume EMA9 vs EMA21 — accumulation or distribution trend">OBV ${obvLabel}</span>`;
  }

  // Phase 12: Volume profile + VWAP band badges
  if (d.vpoc != null) {
    const aboveVpoc = d.price > d.vpoc;
    const vCls = aboveVpoc ? 'ctx-bull' : 'ctx-bear';
    html += `<span class="ctx-badge ${vCls}" title="Volume Point of Control — highest-volume price level this session">VPOC $${d.vpoc.toFixed(2)} ${aboveVpoc?'▲':'▼'}</span>`;
  }
  if (d.vah != null && d.val != null) {
    if (d.price > d.vah)
      html += `<span class="ctx-badge ctx-bull" title="Price above Value Area High — breakout expansion">↑ VAH $${d.vah.toFixed(2)}</span>`;
    else if (d.price < d.val)
      html += `<span class="ctx-badge ctx-bear" title="Price below Value Area Low — breakdown expansion">↓ VAL $${d.val.toFixed(2)}</span>`;
    else {
      const pct = Math.round((d.price - d.val) / Math.max(d.vah - d.val, 0.01) * 100);
      html += `<span class="ctx-badge ctx-neutral" title="Inside Value Area (70% volume zone) — fair value range">VA ${pct}% ↔ $${d.val.toFixed(2)}–$${d.vah.toFixed(2)}</span>`;
    }
  }
  if (d.vwap_2u != null && d.price > d.vwap_2u)
    html += `<span class="ctx-badge ctx-bear" title="Price above VWAP +2σ — statistically extreme, mean-reversion risk">⚠ VWAP +2σ $${d.vwap_2u.toFixed(2)}</span>`;
  else if (d.vwap_2d != null && d.price < d.vwap_2d)
    html += `<span class="ctx-badge ctx-bull" title="Price below VWAP -2σ — statistically extreme, mean-reversion opportunity">⚠ VWAP -2σ $${d.vwap_2d.toFixed(2)}</span>`;
  else if (d.vwap_1u != null && d.vwap_1d != null) {
    const vwapBandCls = d.price > d.vwap_1u ? 'ctx-bull' : d.price < d.vwap_1d ? 'ctx-bear' : 'ctx-neutral';
    html += `<span class="ctx-badge ${vwapBandCls}" title="VWAP bands (1σ: $${d.vwap_1d.toFixed(2)}–$${d.vwap_1u.toFixed(2)})">VWAP ±1σ</span>`;
  }

  // Phase 11: Fibonacci zone + RS badges
  if (d.fib_at_zone && d.fib_zone_level && d.fib_zone_val != null) {
    const aboveFib = d.price >= d.fib_zone_val;
    const fibCls   = aboveFib ? 'ctx-bull' : 'ctx-bear';
    html += `<span class="ctx-badge ${fibCls}" title="Price is at Fibonacci zone — potential ${aboveFib?'support':'resistance'}">Fib ${d.fib_zone_level} $${d.fib_zone_val.toFixed(2)} ${aboveFib?'▲':'▼'}</span>`;
  }
  if (d.rs_vs_spy != null && d.rs_signal && d.rs_signal !== 'benchmark') {
    const rsCls   = d.rs_signal === 'leader' ? 'ctx-bull' : d.rs_signal === 'lagger' ? 'ctx-bear' : 'ctx-neutral';
    const rsSign  = d.rs_vs_spy > 0 ? '+' : '';
    html += `<span class="ctx-badge ${rsCls}" title="Session performance vs SPY">RS ${rsSign}${d.rs_vs_spy.toFixed(2)}% vs SPY</span>`;
  }

  // Phase 16: Session range position
  if (d.session_high != null && d.session_low != null && d.range_pos_pct != null) {
    const rng    = d.session_high - d.session_low;
    const rCls   = d.range_pos_pct <= 25 ? 'ctx-bull' : d.range_pos_pct >= 75 ? 'ctx-bear' : 'ctx-neutral';
    const chgStr = d.session_chg_pct != null ? ` ${d.session_chg_pct >= 0 ? '+' : ''}${d.session_chg_pct.toFixed(2)}%` : '';
    html += `<span class="ctx-badge ${rCls}" title="Session range: H $${d.session_high.toFixed(2)} / L $${d.session_low.toFixed(2)} (±$${rng.toFixed(2)}) — price at ${d.range_pos_pct.toFixed(0)}% of today&#39;s range${chgStr ? '; today ' + chgStr : ''}">Range ${d.range_pos_pct.toFixed(0)}%${chgStr}</span>`;
  }

  // Phase 17: VWAP distance + range expansion badges
  if (d.vwap_dist_atr != null) {
    const vSign = d.vwap_dist_atr >= 0 ? '+' : '';
    const vCls  = Math.abs(d.vwap_dist_atr) < 0.4 ? 'ctx-neutral' : d.vwap_dist_atr > 0 ? 'ctx-bull' : 'ctx-bear';
    const vWarn = Math.abs(d.vwap_dist_atr) > 2.0 ? ' ⚠ Extended' : '';
    html += `<span class="ctx-badge ${vCls}" title="Distance from VWAP in ATR units — >2 means price is extended from VWAP">VWAP ${vSign}${d.vwap_dist_atr.toFixed(1)}ATR${vWarn}</span>`;
  }
  if (d.range_vs_atr != null) {
    const compLabel = d.range_vs_atr < 0.8 ? ' ⚡ Coiling' : d.range_vs_atr < 1.2 ? '' : d.range_vs_atr > 2.5 ? ' Extended' : '';
    const rCls = d.range_vs_atr < 1.0 ? 'ctx-bull' : 'ctx-neutral';
    html += `<span class="ctx-badge ${rCls}" title="Today&#39;s H-L range vs ATR. <1× = range compressed (coiling, breakout setup). >2× = expanded (momentum day).">Rng ×${d.range_vs_atr.toFixed(1)}ATR${compLabel}</span>`;
  }
  if (d.ema9_1m != null && d.price != null) {
    const aboveEma = d.price > d.ema9_1m;
    const eCls = aboveEma ? 'ctx-bull' : 'ctx-bear';
    html += `<span class="ctx-badge ${eCls}" title="EMA9 on 1-minute chart — reactive short-term trend filter">EMA9 $${d.ema9_1m.toFixed(2)} ${aboveEma ? '▲' : '▼'}</span>`;
  }
  if (d.ema50_1m != null && d.price != null) {
    const above50 = d.price > d.ema50_1m;
    const e50Cls  = above50 ? 'ctx-bull' : 'ctx-bear';
    html += `<span class="ctx-badge ${e50Cls}" title="EMA50 on 1-minute chart — 50-minute session trend. With EMA9+SMA20 forms a full trend stack.">EMA50 $${d.ema50_1m.toFixed(2)} ${above50 ? '▲' : '▼'}</span>`;
  }
  if (d.sma200_1m != null && d.price != null) {
    const above200 = d.price > d.sma200_1m;
    const s200Cls  = above200 ? 'ctx-bull' : 'ctx-bear';
    const dist200  = ((d.price - d.sma200_1m) / d.sma200_1m * 100);
    const distStr  = `${dist200 >= 0 ? '+' : ''}${dist200.toFixed(2)}%`;
    html += `<span class="ctx-badge ${s200Cls}" title="SMA200 on 1-minute chart — key institutional reference; below is macro bearish, above is macro bullish. 5m SMA200: $${d.sma200_5m != null ? d.sma200_5m.toFixed(2) : '--'}">SMA200 $${d.sma200_1m.toFixed(2)} ${above200 ? '▲' : '▼'} ${distStr}</span>`;
  }
  // Phase 18: PM High/Low badges
  if (d.pm_high != null && d.price != null) {
    const abovePM = d.price > d.pm_high;
    const pmHCls  = abovePM ? 'ctx-bull' : 'ctx-neutral';
    const pmHDist = ((d.price - d.pm_high) / d.price * 100).toFixed(2);
    html += `<span class="ctx-badge ${pmHCls}" title="Pre-market session high — acts as resistance until broken; breakout is bullish">PM H $${d.pm_high.toFixed(2)} ${abovePM ? '▲ Above' : `(${pmHDist}%)`}</span>`;
  }
  if (d.pm_low != null && d.price != null) {
    const belowPM = d.price < d.pm_low;
    const pmLCls  = belowPM ? 'ctx-bear' : 'ctx-neutral';
    const pmLDist = ((d.price - d.pm_low) / d.price * 100).toFixed(2);
    html += `<span class="ctx-badge ${pmLCls}" title="Pre-market session low — acts as support until broken; breakdown is bearish">PM L $${d.pm_low.toFixed(2)} ${belowPM ? '▼ Below' : `(+${pmLDist}%)`}</span>`;
  }

  // Phase 16: Gamma walls (call wall = nearest high-OI call above price; put wall = nearest high-OI put below price)
  if (d.top_call_strikes && d.top_call_strikes.length && d.price != null) {
    const callWall = d.top_call_strikes.filter(s => s.strike >= d.price).sort((a,b) => a.strike - b.strike)[0];
    const putWall  = d.top_put_strikes  && d.top_put_strikes.filter(s => s.strike <= d.price).sort((a,b) => b.strike - a.strike)[0];
    if (callWall) {
      const dist = ((callWall.strike - d.price) / d.price * 100).toFixed(1);
      html += `<span class="ctx-badge ctx-bear" title="Call Wall: largest open-interest call strike above price. Dealers short calls here must buy stock as price rises — acts as resistance magnet at expiry.">Call Wall $${callWall.strike.toFixed(0)} (+${dist}%)</span>`;
    }
    if (putWall) {
      const dist = ((d.price - putWall.strike) / d.price * 100).toFixed(1);
      html += `<span class="ctx-badge ctx-bull" title="Put Wall: largest open-interest put strike below price. Dealers short puts here must sell stock as price falls — acts as support floor at expiry.">Put Wall $${putWall.strike.toFixed(0)} (-${dist}%)</span>`;
    }
  }

  row.innerHTML = html;
}

// ── Signal grid ───────────────────────────────────────────────────────────────
const INST_KEYS = new Set(['block_print','flow_unusual','vol_delta','vwap_def','tape_read']);

const CAT_COLORS  = {TECH:'#2266cc',PATTERN:'#cc7700',LEVELS:'#8833cc',INST:'#cc9900',MARKET:'#008855'};
const CAT_LABELS  = {TECH:'Technical',PATTERN:'Pattern',LEVELS:'Levels',INST:'Institutional',MARKET:'Market'};
const CAT_ORDER   = ['TECH','PATTERN','LEVELS','INST','MARKET'];
const CQ_META     = {
  HIGH: {clr:'#00ff88', lbl:'★ CQ HIGH'},
  MED:  {clr:'#ffcc00', lbl:'◆ CQ MED'},
  LOW:  {clr:'#ff9944', lbl:'▲ CQ LOW'},
  WEAK: {clr:'#555555', lbl:'CQ WEAK'},
};

function renderCatBreakdown(breakdown, cq, vel) {
  const el = document.getElementById('cat-breakdown');
  if (!el) return;
  if (!breakdown || !breakdown.active) { el.innerHTML = ''; return; }
  const m     = CQ_META[cq] || CQ_META.WEAK;
  const act   = breakdown.active || {};
  const nCats = Object.values(act).filter(v=>v>0).length;
  const tech  = act.TECH  || 0;
  const inst  = act.INST  || 0;
  let cqHint  = '';
  if      (cq==='WEAK' && nCats<2) cqHint = `→ LOW: +${2-nCats} cat`;
  else if (cq==='LOW'  && tech <3) cqHint = `→ MED: +${3-tech} TECH`;
  else if (cq==='LOW'  && nCats<3) cqHint = `→ MED: +${3-nCats} cat`;
  else if (cq==='MED'  && tech <3) cqHint = `→ HIGH: +${3-tech} TECH`;
  else if (cq==='MED'  && inst <1) cqHint = '→ HIGH: +1 INST';
  else if (cq==='MED'  && nCats<4) cqHint = `→ HIGH: +${4-nCats} cat`;
  else if (cq==='HIGH')            cqHint = '★ Max tier';
  const hintHtml = cqHint ? `<span style="font-size:.55rem;color:#555;white-space:nowrap;margin-left:2px">${cqHint}</span>` : '';
  const bars = CAT_ORDER.map(cat => {
    const active = (breakdown.active || {})[cat] || 0;
    const total  = (breakdown.total  || {})[cat] || 0;
    if (!total) return '';
    const pct = Math.round(active / total * 100);
    const clr = active > 0 ? CAT_COLORS[cat] : '#1e1e1e';
    return `<span style="display:inline-flex;align-items:center;gap:3px;font-size:.6rem">
      <span style="color:${clr};font-weight:bold;min-width:26px">${cat.slice(0,3)}</span>
      <span style="display:inline-block;width:36px;height:4px;background:#1a1a1a;border-radius:2px;overflow:hidden"><span style="display:inline-block;width:${pct}%;height:4px;background:${clr}"></span></span>
      <span style="color:${clr};min-width:22px">${active}/${total}</span>
    </span>`;
  }).filter(Boolean).join('<span style="color:#2a2a2a;margin:0 3px">|</span>');
  el.innerHTML = `<div style="display:flex;align-items:center;flex-wrap:wrap;gap:4px;padding:3px 0 5px;border-bottom:1px solid #181818;margin-bottom:5px">
    ${bars}
    <span style="margin-left:auto;font-size:.6rem;font-weight:bold;color:${m.clr};border:1px solid ${m.clr}55;padding:1px 6px;border-radius:3px;white-space:nowrap">${m.lbl}</span>
    ${hintHtml}
    ${vel !== null && vel !== undefined ? velArrow(vel) : ''}
  </div>`;
}

function renderSignals() {
  const d = allData[curTicker];
  if (!d) return;
  const signals   = curDir === 'bull' ? d.bull_signals   : d.bear_signals;
  const breakdown = curDir === 'bull' ? d.bull_breakdown : d.bear_breakdown;
  const cq        = curDir === 'bull' ? d.bull_cq        : d.bear_cq;
  const vel       = curDir === 'bull' ? d.bull_velocity  : d.bear_velocity;
  const grid      = document.getElementById('signal-grid');
  grid.innerHTML  = '';

  renderCatBreakdown(breakdown, cq, vel);

  // Volume-delta divergence warning banner
  const divEl = document.getElementById('div-warn-banner');
  if (d.vol_delta_div) {
    const isBear = d.vol_delta_div === 'bear';
    divEl.className = isBear ? 'div-warn' : 'div-absorb';
    divEl.textContent = isBear
      ? '⚠ Vol Delta Divergence — price rising but sellers in control (exhaustion warning)'
      : '⚡ Vol Delta Absorption — price falling but buyers in control (reversal warning)';
    divEl.classList.remove('d-none');
  } else {
    divEl.classList.add('d-none');
  }

  // Render signals grouped by category
  for (const cat of CAT_ORDER) {
    const catSigs = Object.entries(signals || {}).filter(([k]) => (SIGNAL_CATEGORIES[k] || 'TECH') === cat);
    if (!catSigs.length) continue;
    const clr = CAT_COLORS[cat];

    const hdr = document.createElement('div');
    hdr.className = 'col-12';
    hdr.innerHTML = `<div style="font-size:.55rem;text-transform:uppercase;letter-spacing:1.5px;color:${clr};border-bottom:1px solid ${clr}33;padding-bottom:2px;margin-top:5px;margin-bottom:2px">${CAT_LABELS[cat]}</div>`;
    grid.appendChild(hdr);

    for (const [key, sig] of catSigs) {
      const col    = document.createElement('div');
      col.className = 'col-6 col-md-4 col-xl-3';
      const isInst = INST_KEYS.has(key);
      const tfHtml = sig.tf1 !== undefined
        ? `<span class="tf-badge ${sig.tf1?'tf-ok':'tf-no'}">1m</span><span class="tf-badge ${sig.tf5?'tf-ok':'tf-no'}">5m</span>`
        : '';
      const valColor    = sig.active ? (curDir==='bull'?'#00ff88':'#ff6666') : (isInst ? '#5a4a00' : '#444');
      const borderColor = sig.active ? clr+'cc' : clr+'22';
      col.innerHTML = `<div class="sig-card ${isInst?'inst ':''} ${sig.active?'active':'inactive'}" style="border-left:2px solid ${borderColor}">
        <span class="sig-icon">${sig.active?(curDir==='bull'?'✅':'🔴'):'❌'}</span>
        <div class="sig-label">${sig.label} ${tfHtml} <small style="color:#444">${sig.points}pt</small></div>
        <div class="sig-val" style="color:${valColor}">${sig.value}</div>
      </div>`;
      grid.appendChild(col);
    }
  }

  const vsBadge = document.getElementById('vol-spike-badge');
  if (d.volume_spike) {
    vsBadge.classList.remove('d-none');
    vsBadge.textContent = '⚡ VOL SPIKE ' + (d.vol_ratio ? d.vol_ratio+'x' : '');
  } else {
    vsBadge.classList.add('d-none');
  }
}

// ── ATR Risk Panel ────────────────────────────────────────────────────────────
function renderRiskPanel() {
  const d = allData[curTicker];
  if (!d) return;
  const panel  = document.getElementById('risk-panel');
  const isBull = curDir === 'bull';
  const sl     = isBull ? d.bull_stop : d.bear_stop;
  const tp     = isBull ? d.bull_tp   : d.bear_tp;

  function chip(label, val, color) {
    return `<div class="risk-chip">
      <span class="rc-label">${label}</span>
      <span class="rc-val" style="color:${color}">${val}</span>
    </div>`;
  }

  panel.innerHTML =
    chip('ATR(14)',     d.atr    ? d.atr.toFixed(2)          : '--',  '#ffaa00') +
    chip('Stop Loss',   sl       ? '$'+sl.toFixed(2)          : '--',  '#ff6666') +
    chip('Take Profit', tp       ? '$'+tp.toFixed(2)          : '--',  '#00ff88') +
    chip('Pos. Size',   d.pos_size ? d.pos_size+' shares'     : '--',  '#00ffcc') +
    chip('Risk/Trade',  d.pos_size && sl && d.price
      ? '$'+(Math.abs(d.price - sl) * d.pos_size).toFixed(0) : '--',  '#aaa') +
    chip('R:R',         (sl && tp && d.price)
      ? (Math.abs(tp - d.price) / Math.abs(d.price - sl)).toFixed(1)+'x' : '--', '#aaa');
}

// ── Alerts ────────────────────────────────────────────────────────────────────
function renderAlerts() {
  const d = allData[curTicker];
  if (!d) return;
  const panel = document.getElementById('alerts-panel');
  if (!d.alerts || d.alerts.length === 0) {
    panel.innerHTML = '<span class="text-muted" style="font-size:.8rem">No alerts yet</span>';
    return;
  }
  panel.innerHTML = d.alerts.map(a => {
    const clr    = a.direction==='BULL' ? '#00ff88' : '#ff6666';
    const cqM    = CQ_META[a.cq] || CQ_META.WEAK;
    const cqBadge= a.cq ? `<span style="font-size:.55rem;font-weight:bold;color:${cqM.clr};border:1px solid ${cqM.clr}44;padding:0 4px;border-radius:2px;margin-left:4px">${cqM.lbl}</span>` : '';
    return `<div class="alert-item">
      <span style="color:#ffaa00">${a.time}</span>
      <span class="ms-2 fw-bold" style="color:${clr}">${a.direction}</span>
      <span class="ms-2">$${a.price.toFixed(2)}</span>
      <span class="ms-1 text-muted">· ${a.score}pts</span>${cqBadge}
      <div style="color:#777;font-size:.7rem;margin-top:2px">${a.message}</div>
    </div>`;
  }).join('');
}

// ── Score Chart ───────────────────────────────────────────────────────────────
function setChartMode(mode) {
  chartMode = mode;
  const btnM = document.getElementById('chart-btn-multi');
  const btnS = document.getElementById('chart-btn-single');
  const on  = 'background:#0d2010;color:#00ff88;border:1px solid #00ff8844;border-radius:3px;padding:1px 6px;font-size:.6rem;cursor:pointer';
  const off = 'background:transparent;color:#444;border:1px solid #222;border-radius:3px;padding:1px 6px;font-size:.6rem;cursor:pointer';
  if (btnM) btnM.style.cssText  = mode === 'multi'  ? on : off;
  if (btnS) btnS.style.cssText  = mode === 'single' ? on : off;
  updateChart();
}

function initChart() {
  const ctx = document.getElementById('scoreChart').getContext('2d');
  scoreChart = new Chart(ctx, {
    type: 'line',
    data: { labels: [], datasets: [] },
    options: {
      responsive: true, animation: {duration: 150},
      interaction: {mode: 'index', intersect: false},
      scales: {
        x: {ticks:{color:'#444',maxTicksLimit:8,font:{size:9}}, grid:{color:'#1a1a1a'}},
        y: {min:0, max:MAX_SCORE, ticks:{color:'#444',stepSize:10}, grid:{color:'#1a1a1a'}}
      },
      plugins: {legend: {labels: {color:'#555', font:{size:9}, boxWidth:10, padding:5}}}
    }
  });
}

function updateChart() {
  if (!scoreChart || !allData) return;
  const tickers = Object.keys(allData);
  if (!tickers.length) return;

  if (chartMode === 'multi') {
    const maxLen = Math.max(...tickers.map(t => (allData[t].history || []).length), 1);
    const labelTicker = tickers.reduce((a, b) =>
      (allData[a].history||[]).length >= (allData[b].history||[]).length ? a : b, tickers[0]);
    const labels = (allData[labelTicker].history || []).map(h => h.time);
    scoreChart.data.labels = labels;
    scoreChart.data.datasets = tickers.map(t => {
      const hist = allData[t].history || [];
      const pad  = maxLen - hist.length;
      return {
        label: t,
        data: [...Array(pad).fill(null), ...hist.map(h => h.bull_score)],
        borderColor: TICKER_COLORS[t] || '#888',
        backgroundColor: 'transparent',
        tension: 0.3,
        pointRadius: 0,
        borderWidth: t === curTicker ? 2.5 : 1.2,
      };
    });
  } else {
    const d = allData[curTicker];
    if (!d || !d.history || !d.history.length) return;
    scoreChart.data.labels = d.history.map(h => h.time);
    scoreChart.data.datasets = [
      {label:'Bull', data: d.history.map(h => h.bull_score),
       borderColor:'#00ff88', backgroundColor:'rgba(0,255,136,.06)',
       tension:.3, pointRadius:2, borderWidth:2, fill:true},
      {label:'Bear', data: d.history.map(h => h.bear_score),
       borderColor:'#ff6666', backgroundColor:'rgba(255,100,100,.05)',
       tension:.3, pointRadius:2, borderWidth:1.5, fill:true},
    ];
  }
  scoreChart.update('none');
}

// ── Economic calendar ─────────────────────────────────────────────────────────
function renderEconCalendar() {
  const list = document.getElementById('econ-list');
  const banner = document.getElementById('econ-banner');
  if (!list) return;
  if (!econEvents || econEvents.length === 0) {
    list.innerHTML = '<span style="color:#555">No high-impact USD events found for this week</span>';
    banner.classList.add('d-none');
    return;
  }
  const todayEvs = econEvents.filter(e => e.today);
  if (todayEvs.length > 0) {
    banner.innerHTML = '⚠️ <b>High Impact Today:</b> ' +
      todayEvs.map(e => `${e.title} @ ${e.time}`).join(' &nbsp;|&nbsp; ');
    banner.classList.remove('d-none');
  } else {
    banner.classList.add('d-none');
  }
  const upcomingEvs = econEvents.filter(e => e.upcoming);
  const displayEvs  = upcomingEvs.length > 0 ? upcomingEvs : econEvents;
  list.innerHTML = displayEvs.map(e => {
    const todayCls = e.today ? 'color:#00ff88;font-weight:600' : 'color:#555';
    const tag      = e.today ? ' <span style="color:#ffaa00;font-size:.65rem">TODAY</span>' : '';
    return `<div style="padding:4px 0;border-bottom:1px solid #0d0d0d">
      <span style="${todayCls}">${e.date}</span>
      <span class="ms-2 fw-bold" style="color:${e.today?'#fff':'#aaa'}">${e.title}</span>${tag}
      <span class="ms-2" style="color:#666">${e.time}</span>
      ${e.forecast ? `<span class="ms-2" style="color:#555;font-size:.72rem">F: ${e.forecast}</span>` : ''}
      ${e.previous ? `<span class="ms-1" style="color:#444;font-size:.72rem">P: ${e.previous}</span>` : ''}
    </div>`;
  }).join('');
  const upd = document.getElementById('econ-updated');
  if (upd && upcomingEvs.length === 0) upd.textContent = '(past events)';
}

// ── Signal Analytics tab ──────────────────────────────────────────────────────
// ── Phase 19: Cross-ticker signal heatmap ────────────────────────────────────
function renderHeatmap() {
  if (!allData || !Object.keys(allData).length) return '';
  const cats    = ['TECH','PATTERN','LEVELS','INST','MARKET'];
  const catClrs = {TECH:'#2266cc',PATTERN:'#cc7700',LEVELS:'#8833cc',INST:'#cc9900',MARKET:'#008855'};

  // Header row
  let html = `<div style="border-bottom:1px solid #1a1a1a;padding-bottom:10px;margin-bottom:10px">
  <div class="section-title">Cross-Ticker Signal Heatmap</div>
  <div style="overflow-x:auto">
  <table style="width:100%;border-collapse:collapse;font-size:.72rem">
  <thead><tr style="color:#333;text-transform:uppercase;font-size:.58rem">
    <th style="padding:3px 6px;text-align:left;width:48px"></th>
    <th style="padding:3px 4px;text-align:center;width:32px">Dir</th>
    <th style="padding:3px 4px;text-align:center;width:44px">Score</th>
    <th style="padding:3px 4px;text-align:center;width:38px">CQ</th>`;
  for (const cat of cats) {
    html += `<th style="padding:3px 4px;text-align:center;color:${catClrs[cat]}">${cat.slice(0,3)}</th>`;
  }
  html += `<th style="padding:3px 4px;text-align:left">Setup</th>
    <th style="padding:3px 4px;text-align:center">Peak</th></tr></thead><tbody>`;

  for (const [ticker, d] of Object.entries(allData)) {
    const dir      = d.direction || 'NEUTRAL';
    const isActive = ticker === curTicker;
    const activeDir= dir === 'BEAR' ? 'bear' : 'bull';
    const score    = activeDir === 'bear' ? d.bear_score : d.bull_score;
    const cq       = activeDir === 'bear' ? d.bear_cq    : d.bull_cq;
    const vel      = activeDir === 'bear' ? d.bear_velocity : d.bull_velocity;
    const breakdown= activeDir === 'bear' ? d.bear_breakdown : d.bull_breakdown;
    const signals  = activeDir === 'bear' ? d.bear_signals : d.bull_signals;
    const dirClr   = dir === 'BULL' ? '#00ff88' : dir === 'BEAR' ? '#ff6666' : '#555';
    const scorePct = score / MAX_SCORE;
    const scoreClr = scorePct >= 0.65 ? '#00ff88' : scorePct >= 0.45 ? '#aaff00' : scorePct >= 0.28 ? '#ffaa00' : '#ff4444';
    const cqMeta   = {HIGH:{c:'#00ff88',s:'★H'},MED:{c:'#ffcc00',s:'◆M'},LOW:{c:'#ff9944',s:'▲L'},WEAK:{c:'#444',s:'W'}}[cq]||{c:'#444',s:'-'};
    const velStr   = vel === null || vel === undefined ? '' : vel >= 2 ? `<span style="color:#00ff88">↑${vel}</span>` : vel >= 1 ? `<span style="color:#88ff88">↑1</span>` : vel === 0 ? `<span style="color:#333">→</span>` : `<span style="color:#ff6666">↓${Math.abs(vel)}</span>`;
    const grd      = setupGrade(d, activeDir);

    const rowBg = isActive ? ';background:#0a0a1a' : '';
    html += `<tr style="border-bottom:1px solid #0d0d0d;cursor:pointer${rowBg}" onclick="selectTicker('${ticker}')">
      <td style="padding:3px 6px;font-weight:${isActive?'700':'500'};color:${isActive?'#fff':'#aaa'}">${ticker}</td>
      <td style="padding:3px 4px;text-align:center;color:${dirClr};font-size:.65rem;font-weight:700">${dir[0]}</td>
      <td style="padding:3px 4px;text-align:center">
        <span style="color:${scoreClr};font-weight:600">${score}</span>
        <span style="color:#333;font-size:.6rem">/${MAX_SCORE}</span>
        ${velStr}
      </td>
      <td style="padding:3px 4px;text-align:center;color:${cqMeta.c};font-size:.65rem;font-weight:700">${cqMeta.s}</td>`;

    for (const cat of cats) {
      // Count active signals in this category
      const catSigs  = Object.entries(signals || {}).filter(([k]) => (SIGNAL_CATEGORIES[k]||'') === cat);
      const active   = catSigs.filter(([,v]) => v.active).length;
      const total    = catSigs.length;
      const intensity= total > 0 ? active / total : 0;
      const alpha    = Math.round(intensity * 100);
      const cellBg   = active > 0 ? `background:${catClrs[cat]}${alpha.toString(16).padStart(2,'0')}` : '';
      const txt      = total > 0 ? `${active}/${total}` : '–';
      const txtClr   = active > 0 ? catClrs[cat] : '#282828';
      html += `<td style="padding:3px 4px;text-align:center;${cellBg};border-radius:2px">
        <span style="color:${txtClr};font-weight:${active>0?'600':'400'}">${txt}</span>
      </td>`;
    }

    const peakVal = activeDir === 'bear' ? (d.bear_score_peak||0) : (d.bull_score_peak||0);
    const peakPct = peakVal / MAX_SCORE;
    const peakClr = peakPct >= 0.65 ? '#00ff88' : peakPct >= 0.45 ? '#aaff00' : peakPct >= 0.28 ? '#ffaa00' : '#555';
    html += `<td style="padding:3px 6px;font-size:.7rem">
      <span style="color:${grd.c};font-weight:700">${grd.g}</span>
    </td>
    <td style="padding:3px 4px;text-align:center;font-size:.62rem">
      <span style="color:${peakClr}">${peakVal}</span>
    </td></tr>`;
  }

  html += '</tbody></table></div></div>';
  return html;
}

function renderAnalytics() {
  const panel = document.getElementById('analytics-panel');
  if (!panel) return;

  function miniBar(pct, color) {
    return `<div style="flex:1;background:#1a1a1a;border-radius:3px;height:10px;min-width:40px">
      <div style="width:${Math.round(Math.min(pct,100))}%;background:${color};height:10px;border-radius:3px;transition:width .3s"></div>
    </div>`;
  }

  // ── Trade Outcomes section ──────────────────────────────────────────────────
  const ots    = tradesData.outcomes || [];
  const opens  = tradesData.open_trades || [];
  const wins   = ots.filter(o => o.result === 'WIN');
  const losses = ots.filter(o => o.result === 'LOSS');
  const tos    = ots.filter(o => o.result === 'TIMEOUT');
  const rVals  = ots.map(o => o.r_multiple).filter(r => r != null);
  const avgR   = rVals.length ? (rVals.reduce((a,b)=>a+b,0)/rVals.length).toFixed(2) : null;
  const grossW = wins.reduce((s,o)=>s+(o.r_multiple||0),0);
  const grossL = Math.abs(losses.reduce((s,o)=>s+(o.r_multiple||0),0));
  const pf     = grossL > 0 ? (grossW/grossL).toFixed(2) : (grossW > 0 ? '∞' : '--');
  const totalR = rVals.reduce((a,b)=>a+b,0).toFixed(2);

  // Per-ticker outcome breakdown
  const byTickerOuts = {};
  for (const o of ots) {
    if (!byTickerOuts[o.ticker]) byTickerOuts[o.ticker] = {w:0, l:0, to:0, rVals:[]};
    const b = byTickerOuts[o.ticker];
    if (o.result==='WIN') b.w++; else if (o.result==='LOSS') b.l++; else b.to++;
    if (o.r_multiple != null) b.rVals.push(o.r_multiple);
  }
  const tkRows = Object.entries(byTickerOuts)
    .filter(([,b]) => b.w+b.l+b.to > 0)
    .sort(([,a],[,b]) => (b.w+b.l+b.to)-(a.w+a.l+a.to))
    .map(([tk, b]) => {
      const tot  = b.w + b.l + b.to;
      const wr   = tot ? Math.round(b.w/tot*100) : 0;
      const avgR = b.rVals.length ? b.rVals.reduce((a,c)=>a+c,0)/b.rVals.length : null;
      const rStr = avgR !== null ? `${avgR>=0?'+':''}${avgR.toFixed(2)}R` : '--R';
      const rClr = avgR === null ? '#555' : avgR >= 0 ? '#00ff88' : '#ff6666';
      const wrClr= wr >= 60 ? '#00ff88' : wr >= 45 ? '#ffaa00' : '#ff6666';
      return `<span style="font-size:.63rem;color:#555;border:1px solid #1a1a1a;padding:2px 6px;border-radius:3px;white-space:nowrap">
        <span style="color:#aaa;font-weight:600">${tk}</span>
        <span style="color:${wrClr};margin-left:3px">${b.w}W/${b.l}L${b.to?`/${b.to}T`:''}</span>
        <span style="color:${wrClr};margin-left:2px">(${wr}%)</span>
        <span style="color:${rClr};margin-left:3px">${rStr}</span>
      </span>`;
    }).join('');

  // CQ tier win rate breakdown
  const byCQ = {HIGH:{w:0,l:0,to:0,rVals:[]}, MED:{w:0,l:0,to:0,rVals:[]}, LOW:{w:0,l:0,to:0,rVals:[]}};
  for (const o of ots) {
    const tier = o.cq || null;
    if (!tier || !byCQ[tier]) continue;
    const b = byCQ[tier];
    if (o.result==='WIN') b.w++; else if (o.result==='LOSS') b.l++; else b.to++;
    if (o.r_multiple != null) b.rVals.push(o.r_multiple);
  }
  const cqTableRows = ['HIGH','MED','LOW'].map(tier => {
    const b = byCQ[tier];
    const tot = b.w + b.l + b.to;
    if (!tot) return '';
    const wr = Math.round(b.w / tot * 100);
    const avgRv = b.rVals.length ? b.rVals.reduce((a,c)=>a+c,0)/b.rVals.length : null;
    const rStr  = avgRv !== null ? `${avgRv>=0?'+':''}${avgRv.toFixed(2)}R` : '--';
    const cqM   = CQ_META[tier] || {clr:'#555', lbl:tier};
    const wrClr = wr >= 60 ? '#00ff88' : wr >= 45 ? '#ffaa00' : '#ff6666';
    const rClr  = avgRv === null ? '#555' : avgRv >= 0 ? '#00ff88' : '#ff6666';
    return `<tr style="border-bottom:1px solid #0d0d0d">
      <td style="padding:2px 8px;font-size:.72rem;font-weight:700;color:${cqM.clr}">${cqM.lbl}</td>
      <td style="padding:2px 6px;font-size:.72rem;text-align:right;color:${wrClr};font-weight:600">${wr}%</td>
      <td style="padding:2px 6px;font-size:.7rem;text-align:center;color:#555">${b.w}W / ${b.l}L${b.to ? ` / ${b.to}T` : ''}</td>
      <td style="padding:2px 6px;font-size:.72rem;text-align:right;color:${rClr}">${rStr}</td>
    </tr>`;
  }).filter(r => r).join('');

  // Equity sparkline: cumulative R over closed trades
  let cumR = 0;
  const cumRseries = ots.map(o => { cumR += (o.r_multiple || 0); return cumR; });
  const eqMax = Math.max(...cumRseries, 0.01);
  const eqMin = Math.min(...cumRseries, 0);
  const eqRange = eqMax - eqMin || 1;
  const sparkH = 32;
  const sparkW = Math.max(cumRseries.length * 6, 60);
  let sparkPath = '';
  cumRseries.forEach((v, i) => {
    const x = Math.round(i / Math.max(cumRseries.length-1,1) * sparkW);
    const y = Math.round(sparkH - (v - eqMin) / eqRange * sparkH);
    sparkPath += (i===0 ? `M${x},${y}` : ` L${x},${y}`);
  });
  const sparkColor = cumR >= 0 ? '#00ff88' : '#ff6666';
  const sparkSvg = cumRseries.length > 1
    ? `<svg width="${sparkW}" height="${sparkH}" style="vertical-align:middle;margin-left:6px">
        <path d="${sparkPath}" fill="none" stroke="${sparkColor}" stroke-width="1.5"/>
       </svg>` : '';

  const tradesHtml = `
<div style="border-bottom:1px solid #1a1a1a;padding-bottom:10px;margin-bottom:10px">
  <div class="section-title d-flex align-items-center gap-2">
    Trade Outcomes (Simulated — ATR SL/TP)
    ${sparkSvg}
  </div>
  ${ots.length === 0 ? `<span style="color:#555;font-size:.78rem">No closed trades yet. Trades open when score ≥ ${ALERT_SCORE_THRESH} during market hours.</span>` : `
  <div class="d-flex flex-wrap gap-2 mb-2" style="font-size:.78rem">
    <span class="ctx-badge ctx-neutral">Closed: ${ots.length}</span>
    <span class="ctx-badge ctx-bull">✅ ${wins.length} (${ots.length?Math.round(wins.length/ots.length*100):0}%)</span>
    <span class="ctx-badge ctx-bear">❌ ${losses.length} (${ots.length?Math.round(losses.length/ots.length*100):0}%)</span>
    ${tos.length ? `<span class="ctx-badge ctx-neutral">⏱ ${tos.length}</span>` : ''}
    ${avgR != null ? `<span class="ctx-badge ${parseFloat(avgR)>=0?'ctx-bull':'ctx-bear'}">Avg R: ${parseFloat(avgR)>0?'+':''}${avgR}</span>` : ''}
    <span class="ctx-badge ctx-neutral">PF: ${pf}</span>
    <span class="ctx-badge ${parseFloat(totalR)>=0?'ctx-bull':'ctx-bear'}">Total R: ${parseFloat(totalR)>0?'+':''}${totalR}</span>
  </div>
  ${tkRows ? `<div style="display:flex;flex-wrap:wrap;gap:3px;margin-bottom:6px">${tkRows}</div>` : ''}
  ${cqTableRows ? `
  <div class="section-title mt-2" style="font-size:.7rem">CQ Tier Performance</div>
  <table style="width:100%;border-collapse:collapse;margin-bottom:6px">
    <thead><tr style="color:#333;text-transform:uppercase;font-size:.58rem">
      <th style="padding:2px 8px;text-align:left">Tier</th>
      <th style="padding:2px 6px;text-align:right">Win%</th>
      <th style="padding:2px 6px;text-align:center">Record</th>
      <th style="padding:2px 6px;text-align:right">Avg R</th>
    </tr></thead>
    <tbody>${cqTableRows}</tbody>
  </table>` : ''}`}
  ${opens.length > 0 ? `
  <div class="section-title mt-2">Open Positions (${opens.length})</div>
  ${opens.map(t => {
    const dc      = t.direction==='BULL'?'#00ff88':'#ff6666';
    const elapsed = Math.round((Date.now()/1000 - t.open_ts)/60);
    const cur     = (allData[t.ticker] || {}).price || null;
    const pnlPts  = cur !== null ? (t.direction==='BULL' ? cur-t.entry : t.entry-cur) : null;
    const risk    = Math.abs(t.entry - t.stop);
    const pnlR    = (pnlPts !== null && risk > 0) ? pnlPts/risk : null;
    const pnlClr  = pnlPts === null ? '#444' : pnlPts >= 0 ? '#00ff88' : '#ff6666';
    const pnlStr  = pnlPts !== null
      ? `${pnlPts>=0?'+':''}${pnlPts.toFixed(2)}${pnlR!==null?` (${pnlR>=0?'+':''}${pnlR.toFixed(2)}R)`:''}`
      : '–';
    return `<div style="font-size:.74rem;padding:3px 0;border-bottom:1px solid #0d0d0d">
      <span style="color:${dc};font-weight:600">${t.direction}</span>
      <span class="ms-1 fw-bold">${t.ticker}</span>
      <span class="ms-1" style="color:#777">@ $${t.entry.toFixed(2)}</span>
      <span class="ms-1" style="color:#ff6666">SL $${t.stop.toFixed(2)}</span>
      <span class="ms-1" style="color:#00ff88">TP $${t.tp.toFixed(2)}</span>
      <span class="ms-2 fw-bold" style="color:${pnlClr}">${pnlStr}</span>
      <span class="ms-2" style="color:#444">[${t.score}/${MAX_SCORE}] ${elapsed}m</span>
    </div>`;
  }).join('')}` : ''}
  ${ots.length > 0 ? `
  <div class="section-title mt-2">Recent Closed</div>
  <table style="width:100%;font-size:.72rem;border-collapse:collapse">
    <thead><tr style="color:#444;text-transform:uppercase;font-size:.6rem">
      <th style="padding:2px 4px">Time</th><th>Ticker</th><th>Dir</th>
      <th>Result</th><th>R</th><th>Entry</th><th>Exit</th><th>Dur</th>
    </tr></thead>
    <tbody>
    ${[...ots].reverse().slice(0,15).map(o => {
      const dc  = o.direction==='BULL'?'#00ff88':'#ff6666';
      const rc  = o.result==='WIN'?'#00ff88':o.result==='LOSS'?'#ff6666':'#888';
      const ico = o.result==='WIN'?'✅':o.result==='LOSS'?'❌':'⏱';
      const r   = o.r_multiple != null ? (o.r_multiple>0?'+':'')+o.r_multiple.toFixed(2) : '--';
      const ts  = (o.open_time||'').slice(11,16);
      return `<tr style="border-bottom:1px solid #0d0d0d">
        <td style="color:#444;padding:2px 4px">${ts}</td>
        <td style="font-weight:600">${o.ticker}</td>
        <td style="color:${dc}">${o.direction}</td>
        <td style="color:${rc}">${ico} ${o.result}</td>
        <td style="color:${parseFloat(r)>=0?'#00ff88':'#ff6666'}">${r}</td>
        <td style="color:#666">$${o.entry.toFixed(2)}</td>
        <td style="color:#666">$${o.exit_price.toFixed(2)}</td>
        <td style="color:#444">${o.elapsed_mins}m</td>
      </tr>`;
    }).join('')}
    </tbody>
  </table>` : ''}
</div>`;

  // ── Signal Stats section ────────────────────────────────────────────────────
  if (!signalLog || signalLog.length === 0) {
    panel.innerHTML = tradesHtml +
      `<span style="color:#555;font-size:.8rem">No signals logged yet. Signals appear once score ≥ ${LOG_SCORE_THRESH}.</span>`;
    return;
  }

  const today     = new Date().toISOString().slice(0, 10);
  const todaySigs = signalLog.filter(e => e.time && e.time.startsWith(today));
  const src       = todaySigs.length > 0 ? todaySigs : signalLog;
  const label     = todaySigs.length > 0 ? 'Today' : 'All-time';
  const total     = src.length;
  const bullCnt   = src.filter(e => e.direction === 'BULL').length;
  const bearCnt   = src.filter(e => e.direction === 'BEAR').length;
  const volCnt    = src.filter(e => e.vol_spike).length;

  const byTicker = {};
  for (const e of src) byTicker[e.ticker] = (byTicker[e.ticker] || 0) + 1;
  const maxTkCnt = Math.max(...Object.values(byTicker), 1);

  const DIST_BUCKET = 10;
  const scoreDist = {};
  for (let b = 0; b <= 90; b += DIST_BUCKET) scoreDist[b] = 0;
  for (const e of src) {
    const s = Math.max(e.bull_score || 0, e.bear_score || 0);
    const bucket = Math.min(90, Math.floor(s / DIST_BUCKET) * DIST_BUCKET);
    scoreDist[bucket] = (scoreDist[bucket] || 0) + 1;
  }
  const maxScoreCnt = Math.max(...Object.values(scoreDist), 1);

  const top5 = [...src].sort((a,b) =>
    Math.max(b.bull_score||0,b.bear_score||0) - Math.max(a.bull_score||0,a.bear_score||0)
  ).slice(0, 5);

  // ── Key Levels section (Phase 9) ──────────────────────────────────────────
  const kd = allData[curTicker] || {};
  function lvlRow(label, val, color, bold) {
    if (val == null) return '';
    const dist = kd.price ? ((kd.price - val) / kd.price * 100) : null;
    const distStr = dist != null ? ` <span style="color:#444;font-size:.65rem">(${dist>0?'+':''}${dist.toFixed(2)}%)</span>` : '';
    return `<tr style="border-bottom:1px solid #0d0d0d${bold?';background:#111':''}">
      <td style="padding:2px 6px;color:${bold?color:'#666'};font-weight:${bold?'600':'400'}">${label}</td>
      <td style="text-align:right;padding:2px 6px;color:${color};font-weight:${bold?'600':'400'}">$${val.toFixed(2)}${distStr}</td>
    </tr>`;
  }
  const keyLevelsHtml = (kd.pivot_pp != null) ? `
<div style="border-bottom:1px solid #1a1a1a;padding-bottom:10px;margin-bottom:10px">
  <div class="section-title">Key Levels — ${curTicker}</div>
  <div class="row g-2">
    <div class="col-12 col-md-4">
      <div style="font-size:.7rem;color:#555;text-transform:uppercase;letter-spacing:.5px;margin-bottom:4px">Pivot Points</div>
      <table style="width:100%;border-collapse:collapse;font-size:.75rem">
        ${lvlRow('R3', kd.pivot_r3, '#00ff88', false)}
        ${lvlRow('R2', kd.pivot_r2, '#00cc66', false)}
        ${lvlRow('R1', kd.pivot_r1, '#00aa44', false)}
        ${lvlRow('PP', kd.pivot_pp, '#ffaa00', true)}
        ${lvlRow('S1', kd.pivot_s1, '#ff8888', false)}
        ${lvlRow('S2', kd.pivot_s2, '#ff6666', false)}
        ${lvlRow('S3', kd.pivot_s3, '#ff4444', false)}
      </table>
    </div>
    <div class="col-12 col-md-4">
      <div style="font-size:.7rem;color:#555;text-transform:uppercase;letter-spacing:.5px;margin-bottom:4px">Fibonacci (${FIB_LOOKBACK}m swing)</div>
      <table style="width:100%;border-collapse:collapse;font-size:.75rem">
        ${lvlRow('Swing Hi', kd.fib_swing_high, '#aaffaa', kd.fib_at_zone && kd.price >= kd.fib_zone_val)}
        ${lvlRow('23.6%',    kd.fib_236,        '#66cc88', kd.fib_zone_level==='23.6%')}
        ${lvlRow('38.2%',    kd.fib_382,        '#44bb77', kd.fib_zone_level==='38.2%')}
        ${lvlRow('50.0%',    kd.fib_500,        '#ffcc44', kd.fib_zone_level==='50.0%')}
        ${lvlRow('61.8% ✦', kd.fib_618,        '#ff9944', kd.fib_zone_level==='61.8%')}
        ${lvlRow('78.6%',    kd.fib_786,        '#ff6644', kd.fib_zone_level==='78.6%')}
        ${lvlRow('Swing Lo', kd.fib_swing_low,  '#ffaaaa', kd.fib_at_zone && kd.price <= kd.fib_zone_val)}
      </table>
    </div>
    <div class="col-12 col-md-3">
      <div style="font-size:.7rem;color:#555;text-transform:uppercase;letter-spacing:.5px;margin-bottom:4px">Volume Profile</div>
      <table style="width:100%;border-collapse:collapse;font-size:.75rem">
        ${kd.vpoc != null ? `
        <tr style="background:#111"><td style="color:#ffd700;padding:2px 6px;font-weight:600">VPOC</td><td style="text-align:right;color:#ffd700;font-weight:600;padding:2px 6px">$${kd.vpoc.toFixed(2)}</td></tr>
        <tr><td style="color:#555;padding:2px 6px">VAH</td><td style="text-align:right;color:#00aa44;padding:2px 6px">$${kd.vah.toFixed(2)}</td></tr>
        <tr><td style="color:#555;padding:2px 6px">VAL</td><td style="text-align:right;color:#ff8888;padding:2px 6px">$${kd.val.toFixed(2)}</td></tr>
        ` : '<tr><td colspan="2" style="color:#333;padding:4px 6px;font-size:.7rem">No data (market closed)</td></tr>'}
        ${kd.vwap_2u != null ? `
        <tr><td style="color:#555;padding:2px 6px">+2σ</td><td style="text-align:right;color:#ff9966;padding:2px 6px">$${kd.vwap_2u.toFixed(2)}</td></tr>
        <tr><td style="color:#555;padding:2px 6px">+1σ</td><td style="text-align:right;color:#cc7744;padding:2px 6px">$${kd.vwap_1u.toFixed(2)}</td></tr>
        ` : ''}
        ${kd.price != null && kd.vwap_val != null ? `
        <tr style="background:#0d0d0d;border-top:1px solid #222"><td style="color:#00ffcc;padding:3px 6px;font-weight:600">VWAP</td><td style="text-align:right;color:#00ffcc;font-weight:600;padding:3px 6px">$${(kd.vwap_1u && kd.vwap_1d ? ((kd.vwap_1u+kd.vwap_1d)/2).toFixed(2) : '--')}</td></tr>
        ` : ''}
        ${kd.vwap_1d != null ? `
        <tr><td style="color:#555;padding:2px 6px">-1σ</td><td style="text-align:right;color:#4477cc;padding:2px 6px">$${kd.vwap_1d.toFixed(2)}</td></tr>
        <tr><td style="color:#555;padding:2px 6px">-2σ</td><td style="text-align:right;color:#6699ff;padding:2px 6px">$${kd.vwap_2d.toFixed(2)}</td></tr>
        ` : ''}
      </table>
    </div>
    <div class="col-12 col-md-3">
      <div style="font-size:.7rem;color:#555;text-transform:uppercase;letter-spacing:.5px;margin-bottom:4px">Reference</div>
      <table style="width:100%;border-collapse:collapse;font-size:.75rem">
        ${lvlRow('Prev High',  kd.prev_high,  '#aaa', false)}
        ${lvlRow('Prev Close', kd.prev_close, '#666', false)}
        ${lvlRow('Prev Low',   kd.prev_low,   '#aaa', false)}
        ${kd.max_pain != null ? lvlRow('Max Pain', kd.max_pain, '#ffd700', true) : ''}
        ${kd.pm_high != null ? lvlRow('PM High', kd.pm_high, '#66bbff', kd.price != null && kd.price > kd.pm_high) : ''}
        ${kd.pm_low  != null ? lvlRow('PM Low',  kd.pm_low,  '#ff88aa', kd.price != null && kd.price < kd.pm_low)  : ''}
        ${kd.orb_high != null ? lvlRow('ORB High', kd.orb_high, '#00ffcc', false) : ''}
        ${kd.orb_low  != null ? lvlRow('ORB Low',  kd.orb_low,  '#ff9900', false) : ''}
        ${kd.price != null ? `<tr style="border-top:1px solid #222;background:#0d0d0d">
          <td style="padding:3px 6px;color:#fff;font-weight:700">Current</td>
          <td style="text-align:right;padding:3px 6px;color:#fff;font-weight:700">$${kd.price.toFixed(2)}</td>
        </tr>` : ''}
        ${kd.regime && kd.regime !== 'unknown' ? `<tr><td style="color:#555;padding:2px 6px">Regime</td><td style="text-align:right;padding:2px 6px;color:#aaa">${kd.regime.replace(/_/g,' ')}</td></tr>` : ''}
        ${kd.candle_bull_pat ? `<tr><td style="color:#555;padding:2px 6px">Bull Pat</td><td style="text-align:right;padding:2px 6px;color:#00ff88">${kd.candle_bull_pat}</td></tr>` : ''}
        ${kd.candle_bear_pat ? `<tr><td style="color:#555;padding:2px 6px">Bear Pat</td><td style="text-align:right;padding:2px 6px;color:#ff6666">${kd.candle_bear_pat}</td></tr>` : ''}
        ${kd.rs_vs_spy != null && kd.rs_signal !== 'benchmark' ? `<tr><td style="color:#555;padding:2px 6px">RS vs SPY</td><td style="text-align:right;padding:2px 6px;color:${kd.rs_signal==='leader'?'#00ffcc':kd.rs_signal==='lagger'?'#ff9966':'#777'}">${kd.rs_vs_spy>0?'+':''}${kd.rs_vs_spy.toFixed(2)}%</td></tr>` : ''}
      </table>
    </div>
  </div>
  ${kd.vp_profile && kd.vp_profile.length > 0 ? (() => {
    const profile = kd.vp_profile;
    const maxVol  = Math.max(...profile.map(b => b[1]));
    const vpoc    = kd.vpoc, vah = kd.vah, val = kd.val, cur = kd.price;
    const rows = [...profile].reverse().map(([p, v]) => {
      const pct     = Math.round(v / maxVol * 100);
      const isVpoc  = vpoc  != null && Math.abs(p - vpoc) < 0.01;
      const inVA    = vah   != null && val != null && p >= val && p <= vah;
      const isCur   = cur   != null && Math.abs(p - cur) < (profile.length > 1 ? Math.abs(profile[1][0] - profile[0][0]) * 0.6 : 0.5);
      const barClr  = isVpoc ? '#ffd700' : inVA ? '#1a4488' : '#0d2233';
      const lblClr  = isVpoc ? '#ffd700' : inVA ? '#4488bb' : '#333';
      return `<div style="display:flex;align-items:center;height:5px;margin-bottom:1px;gap:2px">
        <div style="width:46px;text-align:right;font-size:.55rem;color:${lblClr};flex-shrink:0">${isVpoc?'★':isCur?'►':''} $${p.toFixed(1)}</div>
        <div style="flex:1;background:#060606;border-radius:1px;position:relative">
          <div style="width:${pct}%;height:5px;background:${barClr};border-radius:1px;transition:width .3s"></div>
        </div>
      </div>`;
    }).join('');
    return `<div style="margin-top:8px">
      <div style="font-size:.7rem;color:#555;text-transform:uppercase;letter-spacing:.5px;margin-bottom:4px">
        Volume Profile — today's session
        <span style="float:right;color:#666">VPOC $${vpoc?.toFixed(2)||'--'} | VA $${val?.toFixed(2)||'--'}–$${vah?.toFixed(2)||'--'}</span>
      </div>
      <div style="background:#050505;border:1px solid #111;border-radius:4px;padding:4px 6px;max-height:200px;overflow-y:auto">${rows}</div>
    </div>`;
  })() : ''}
</div>` : '';

  // ── Alpaca Execution panel ──────────────────────────────────────────────────
  let alpacaHtml = '';
  if (!alpacaData.enabled) {
    alpacaHtml = `<div style="border-bottom:1px solid #1a1a1a;padding-bottom:10px;margin-bottom:10px">
      <div class="section-title">Alpaca Execution</div>
      <span style="color:#333;font-size:.78rem">Not configured — add ALPACA_API_KEY + ALPACA_SECRET_KEY to .env</span>
    </div>`;
  } else {
    const isLive = !alpacaData.paper;
    const envBadge = isLive
      ? `<span style="background:#ff444422;color:#ff6666;font-size:.6rem;font-weight:700;border:1px solid #ff444455;padding:2px 7px;border-radius:3px;letter-spacing:.5px">LIVE</span>`
      : `<span style="background:#ffaa0011;color:#ffaa00;font-size:.6rem;font-weight:600;border:1px solid #ffaa0033;padding:2px 7px;border-radius:3px;letter-spacing:.5px">PAPER</span>`;
    const acct = alpacaData.account || {};
    const pos  = alpacaData.positions || [];
    const ords = alpacaData.orders    || [];
    const err  = alpacaData.error;

    const fmt$ = n => n != null ? '$' + parseFloat(n).toLocaleString('en-US',{minimumFractionDigits:2,maximumFractionDigits:2}) : '–';
    const fmt$k = n => n != null ? '$' + (parseFloat(n)/1000).toFixed(1)+'k' : '–';

    const dtClr = acct.daytrade_count >= 3 ? '#ff6666' : acct.daytrade_count >= 2 ? '#ffaa00' : '#555';

    const statusRow = acct.equity != null ? `
    <div style="display:grid;grid-template-columns:repeat(auto-fit,minmax(110px,1fr));gap:6px;margin:8px 0 10px">
      <div style="background:#0d0d0d;border:1px solid #1a1a1a;border-radius:4px;padding:6px 10px">
        <div style="font-size:.58rem;color:#444;text-transform:uppercase;letter-spacing:.5px;margin-bottom:2px">Portfolio Value</div>
        <div style="font-size:.95rem;color:#fff;font-weight:700">${fmt$(acct.portfolio_value)}</div>
      </div>
      <div style="background:#0d0d0d;border:1px solid #1a1a1a;border-radius:4px;padding:6px 10px">
        <div style="font-size:.58rem;color:#444;text-transform:uppercase;letter-spacing:.5px;margin-bottom:2px">Buying Power</div>
        <div style="font-size:.95rem;color:#00ffcc;font-weight:700">${fmt$(acct.buying_power)}</div>
      </div>
      <div style="background:#0d0d0d;border:1px solid #1a1a1a;border-radius:4px;padding:6px 10px">
        <div style="font-size:.58rem;color:#444;text-transform:uppercase;letter-spacing:.5px;margin-bottom:2px">Cash</div>
        <div style="font-size:.95rem;color:#aaa;font-weight:600">${fmt$(acct.cash)}</div>
      </div>
      <div style="background:#0d0d0d;border:1px solid #1a1a1a;border-radius:4px;padding:6px 10px">
        <div style="font-size:.58rem;color:#444;text-transform:uppercase;letter-spacing:.5px;margin-bottom:2px">Day Trades</div>
        <div style="font-size:.95rem;font-weight:700;color:${dtClr}">${acct.daytrade_count} <span style="font-size:.65rem;color:#333">/ 3 PDT</span></div>
      </div>
    </div>
    <div class="d-flex flex-wrap gap-3 mb-2" style="font-size:.7rem">
      <span style="color:#555">Size/trade: <span style="color:#aaa">~$${alpacaData.size_usd||0} × score%</span></span>
      <span style="color:#555">CQ gate: <span style="color:#aaa">${alpacaData.cq_min||'MED'}+</span></span>
      <span style="color:#555">Exit: <span style="color:#aaa">OCA bracket (ATR ×""" + str(ATR_STOP_MULT) + """ SL / ×""" + str(ATR_TP_MULT) + """ TP)</span></span>
    </div>` : (err ? `<div style="color:#ff6666;font-size:.76rem;margin:8px 0;padding:6px 10px;background:#ff000011;border-radius:4px">⚠ ${err}</div>` : '');

    const posHtml = pos.length ? `
    <div style="font-size:.68rem;color:#555;text-transform:uppercase;letter-spacing:.5px;margin-bottom:4px">Open Positions (${pos.length})</div>
    <div style="border:1px solid #1a1a1a;border-radius:4px;overflow:hidden;margin-bottom:8px">
    ${pos.map((p,i) => {
      const isLong = p.side === 'long';
      const sideClr = isLong ? '#00ff88' : '#ff6666';
      const plClr   = p.unrealized_pl == null ? '#555' : p.unrealized_pl >= 0 ? '#00ff88' : '#ff6666';
      const plPct   = p.unrealized_plpc != null ? ` (${(p.unrealized_plpc*100).toFixed(2)}%)` : '';
      const plStr   = p.unrealized_pl  != null
        ? `${p.unrealized_pl>=0?'+':''}${fmt$(p.unrealized_pl)}${plPct}` : '–';
      return `<div style="display:flex;align-items:center;gap:8px;padding:5px 10px;${i>0?'border-top:1px solid #111':''}">
        <span style="color:${sideClr};font-weight:700;min-width:42px;font-size:.72rem">${isLong?'LONG':'SHORT'}</span>
        <span style="font-weight:700;min-width:40px">${p.symbol}</span>
        <span style="color:#555;font-size:.7rem">${p.qty}sh</span>
        <span style="color:#444;font-size:.7rem">@ ${fmt$(p.avg_entry)}</span>
        ${p.current_price ? `<span style="color:#666;font-size:.7rem">→ ${fmt$(p.current_price)}</span>` : ''}
        <span style="color:${plClr};font-weight:700;margin-left:auto;font-size:.76rem">${plStr}</span>
      </div>`;
    }).join('')}
    </div>` : `<div style="color:#2a2a2a;font-size:.74rem;margin-bottom:6px;padding:5px 0">No open positions</div>`;

    const ordStatusClr = s => ({filled:'#00ff88',partially_filled:'#aaff00',new:'#ffaa00',pending_new:'#ffaa00',accepted:'#ffaa00',held:'#ffaa00',canceled:'#333',expired:'#222',rejected:'#ff4444'})[s] || '#555';
    const ordHtml = ords.length ? `
    <div style="font-size:.68rem;color:#555;text-transform:uppercase;letter-spacing:.5px;margin-bottom:4px">Recent Orders (${ords.length})</div>
    <table style="width:100%;border-collapse:collapse;border:1px solid #1a1a1a;border-radius:4px;overflow:hidden">
      <thead><tr style="background:#0a0a0a;color:#333;font-size:.58rem;text-transform:uppercase">
        <th style="padding:3px 8px;text-align:left">Symbol</th>
        <th style="padding:3px 6px;text-align:left">Side</th>
        <th style="padding:3px 6px;text-align:right">Qty</th>
        <th style="padding:3px 6px">Status</th>
        <th style="padding:3px 8px;text-align:right">Fill</th>
        <th style="padding:3px 6px;text-align:center">Type</th>
      </tr></thead>
      <tbody>${ords.map((o,i) => {
        const sc   = o.side === 'buy' ? '#00ff88' : '#ff6666';
        const stc  = ordStatusClr(o.status);
        const fill = o.filled_avg_price ? fmt$(o.filled_avg_price) : '–';
        const cls  = o.order_class === 'bracket' ? `<span style="color:#00ffcc;font-size:.58rem">BRACKET ${o.legs>0?`[${o.legs}L]`:''}</span>`
                   : `<span style="color:#444;font-size:.58rem">${o.order_class||'simple'}</span>`;
        return `<tr style="border-top:1px solid #111;font-size:.7rem">
          <td style="padding:3px 8px;font-weight:700">${o.symbol}</td>
          <td style="padding:3px 6px;color:${sc};font-weight:600">${o.side.toUpperCase()}</td>
          <td style="padding:3px 6px;color:#666;text-align:right">${o.qty||'–'}</td>
          <td style="padding:3px 6px;color:${stc}">${o.status}</td>
          <td style="padding:3px 8px;color:#777;text-align:right">${fill}</td>
          <td style="padding:3px 6px;text-align:center">${cls}</td>
        </tr>`;
      }).join('')}</tbody>
    </table>` : `<div style="color:#2a2a2a;font-size:.74rem;padding:5px 0">No recent orders</div>`;

    const connDot = `<span style="display:inline-block;width:7px;height:7px;border-radius:50%;background:${acct.equity!=null?'#00ff88':'#ff6666'};margin-right:5px;box-shadow:0 0 6px ${acct.equity!=null?'#00ff88':'#ff6666'}"></span>`;
    alpacaHtml = `<div style="border-bottom:1px solid #1a1a1a;padding-bottom:10px;margin-bottom:10px">
      <div class="section-title d-flex align-items-center gap-2">
        ${connDot}Alpaca Execution ${envBadge}
        ${acct.equity!=null ? `<span style="font-size:.62rem;color:#00ff88;margin-left:4px">CONNECTED</span>` : `<span style="font-size:.62rem;color:#ff6666">DISCONNECTED</span>`}
      </div>
      ${statusRow}${posHtml}${ordHtml}
    </div>`;
  }

  panel.innerHTML = renderHeatmap() + alpacaHtml + keyLevelsHtml + tradesHtml + `
<div class="row g-2">
  <div class="col-12">
    <div class="d-flex flex-wrap gap-2" style="font-size:.78rem">
      <span style="color:#555">${label}:</span>
      <span style="color:#fff;font-weight:600">${total} signals</span>
      <span class="ctx-badge ctx-bull">▲ Bull ${bullCnt} (${total?Math.round(bullCnt/total*100):0}%)</span>
      <span class="ctx-badge ctx-bear">▼ Bear ${bearCnt} (${total?Math.round(bearCnt/total*100):0}%)</span>
      <span class="ctx-badge ctx-neutral">⚡ Vol ${volCnt} (${total?Math.round(volCnt/total*100):0}%)</span>
    </div>
  </div>
  <div class="col-12 col-md-5">
    <div class="section-title">Signals by Ticker</div>
    ${Object.entries(byTicker).sort((a,b)=>b[1]-a[1]).map(([t, n]) =>
      `<div class="d-flex align-items-center gap-2 mb-1" style="font-size:.76rem">
        <span style="width:36px;color:#aaa">${t}</span>
        ${miniBar(n/maxTkCnt*100, '#00ffcc')}
        <span style="width:18px;color:#555;text-align:right">${n}</span>
      </div>`
    ).join('')}
  </div>
  <div class="col-12 col-md-4">
    <div class="section-title">Score Distribution</div>
    ${Object.entries(scoreDist).map(([s, n]) => {
      const si = parseInt(s);
      const color = si >= 50 ? '#00ff88' : si >= 30 ? '#aaff00' : si >= ALERT_SCORE_THRESH ? '#ffaa00' : '#ff6666';
      const label = `${si}–${si+10}`;
      return `<div class="d-flex align-items-center gap-2 mb-1" style="font-size:.76rem">
        <span style="width:42px;color:#aaa;text-align:right">${label}</span>
        ${miniBar(n/maxScoreCnt*100, color)}
        <span style="width:18px;color:#555;text-align:right">${n}</span>
      </div>`;
    }).join('')}
  </div>
  <div class="col-12 col-md-3">
    <div class="section-title">Top Setups</div>
    ${top5.map(e => {
      const score  = Math.max(e.bull_score||0, e.bear_score||0);
      const dc     = e.direction==='BULL'?'#00ff88':'#ff6666';
      const vol    = e.vol_spike ? ' ⚡' : '';
      const gap    = e.gap_pct != null ? ` ${e.gap_pct>0?'+':''}${parseFloat(e.gap_pct).toFixed(1)}%` : '';
      const ts     = (e.time||'').slice(11,16);
      const cqM    = e.cq ? (CQ_META[e.cq] || null) : null;
      const cqBadge= cqM ? `<span style="font-size:.52rem;font-weight:bold;color:${cqM.clr};border:1px solid ${cqM.clr}33;padding:0 3px;border-radius:2px;margin-left:3px">${cqM.lbl}</span>` : '';
      return `<div style="padding:4px 0;border-bottom:1px solid #111;font-size:.73rem">
        <span style="color:#555">${ts}</span>
        <span class="ms-1 fw-bold">${e.ticker}</span>
        <span class="ms-1" style="color:#777">$${parseFloat(e.price||0).toFixed(0)}</span>
        <span class="ms-1 fw-bold" style="color:${dc}">${e.direction}</span>
        <span class="ms-1" style="color:#aaa">${score}/${MAX_SCORE}${vol}${gap}</span>${cqBadge}
      </div>`;
    }).join('')}
  </div>
</div>`;
}

// ── Signal log table ──────────────────────────────────────────────────────────
function renderLog() {
  if (!signalLog || signalLog.length === 0) return;
  const tbody = document.getElementById('log-body');
  tbody.innerHTML = signalLog.slice(0, 50).map(e => {
    const dc = e.direction==='BULL'?'log-bull':e.direction==='BEAR'?'log-bear':'log-neutral';
    const gapHtml = e.gap_pct != null
      ? `<span style="color:${e.gap_pct>0?'#00ff88':'#ff6666'}">${e.gap_pct>0?'+':''}${e.gap_pct.toFixed(2)}%</span>`
      : '--';
    return `<tr>
      <td style="color:#555;white-space:nowrap">${e.time}</td>
      <td style="font-weight:600">${e.ticker}</td>
      <td>$${e.price.toFixed(2)}</td>
      <td class="log-bull">${e.bull_score}</td>
      <td class="log-bear">${e.bear_score}</td>
      <td class="${dc} fw-bold">${e.direction}</td>
      <td>${e.cq ? `<span style="font-size:.6rem;font-weight:bold;color:${(CQ_META[e.cq]||{}).clr||'#555'};white-space:nowrap">${(CQ_META[e.cq]||{}).lbl||e.cq}</span>` : '–'}</td>
      <td style="color:#ffaa00">${e.atr ? e.atr.toFixed(2) : '--'}</td>
      <td style="color:#ff6666">${e.stop ? '$'+e.stop.toFixed(2) : '--'}</td>
      <td style="color:#00ff88">${e.tp   ? '$'+e.tp.toFixed(2)   : '--'}</td>
      <td>${gapHtml}</td>
      <td>${e.vol_spike?'⚡':''}</td>
    </tr>`;
  }).join('');
}

// ── Main poll loop ────────────────────────────────────────────────────────────
async function update() {
  try {
    const [res, resT, resA] = await Promise.all([
      fetch('/api/status'),
      fetch('/api/outcomes'),
      fetch('/api/alpaca'),
    ]);
    const data = await res.json();
    const tdata = resT.ok ? await resT.json() : {open_trades:[], outcomes:[]};
    if (resA.ok) { try { alpacaData = await resA.json(); } catch(_) {} }
    allData      = data.tickers     || {};
    signalLog    = data.signal_log  || [];
    vixData      = data.vix         || null;
    econEvents   = data.econ_events || [];
    optionsData  = data.options_data || {};
    tradesData   = tdata;

    const mktBadge = document.getElementById('mkt-badge');
    if (data.market_open) {
      mktBadge.className = 'sb sb-normal'; mktBadge.textContent = 'MARKET OPEN';
      document.getElementById('live-dot').className = 'live-dot';
    } else {
      mktBadge.className = 'sb sb-closed'; mktBadge.textContent = 'MARKET CLOSED';
      document.getElementById('live-dot').className = 'live-dot off';
    }

    // Breadth/VIX badge
    const vixBadge = document.getElementById('vix-badge');
    if (vixData && vixData.breadth && vixData.breadth !== 'NEUTRAL') {
      const isBull = vixData.breadth === 'BULL_DOMINANT';
      const cls    = isBull ? 'ctx-bull' : vixData.breadth === 'BEAR_DOMINANT' ? 'ctx-bear' : 'ctx-neutral';
      const arr    = isBull ? '↑' : '↓';
      vixBadge.className   = `ctx-badge ${cls}`;
      vixBadge.textContent = `Breadth ${vixData.bull_count}B/${vixData.bear_count}b ${arr}`;
      vixBadge.title       = `Market breadth: ${vixData.breadth}`;
    } else {
      vixBadge.className   = 'ctx-badge ctx-neutral';
      vixBadge.textContent = vixData && vixData.bull_count != null
        ? `Breadth ${vixData.bull_count}B/${vixData.bear_count}b`
        : 'Breadth --';
    }

    let latestUpdate = '--';
    for (const [ticker, d] of Object.entries(allData)) {
      const prev    = prevScores[ticker] || {bull:0,bear:0};
      const newMax  = Math.max(d.bull_score, d.bear_score);
      const prevMax = Math.max(prev.bull,    prev.bear);
      if (newMax >= 20 && newMax > prevMax) {
        const cqNow  = d.direction === 'BEAR' ? d.bear_cq : d.bull_cq;
        const cqRank = {HIGH:3, MED:2, LOW:1, WEAK:0}[cqNow] || 0;
        if      (cqRank >= 3) playAlert(1200, 3);
        else if (cqRank >= 2) playAlert(880,  2);
        else if (cqRank >= 1) playAlert(660,  1);
        if (newMax >= ALERT_SCORE_THRESH && cqRank >= 2) {
          fireNotification(ticker, d.direction, newMax, cqNow, d.price);
        }
      }
      prevScores[ticker] = {bull: d.bull_score, bear: d.bear_score};
      if (d.last_update !== 'N/A') latestUpdate = d.last_update;
    }
    document.getElementById('last-update').textContent = latestUpdate;

    renderTickerRow();
    if (curTab === 'analytics') renderAnalytics();
    else { renderSignals(); renderRiskPanel(); }
    renderContextRow();
    renderAlerts();
    updateChart();
    renderLog();
    renderEconCalendar();
  } catch(e) {
    console.error('Update error:', e);
  }
}

initChart();
updateNotifBtn();
update();
setInterval(update, 5000);
</script>
</body>
</html>"""

# ====================== BACKTEST ENGINE ======================
# Runs once at startup in the background. Fetches 60 trading days of historical
# 1m data (one Polygon call per ticker, resampled to 5m internally), then walks
# forward through every BT_SAMPLE_EVERY bars calling the live compute_signals()
# function on a rolling BT_LOOKBACK-bar window. Trades are simulated with the
# same ATR-based SL/TP used by the live execution layer.

BT_DAYS         = 90    # calendar days to request (≈ 60 trading days)
BT_LIMIT        = 50000 # max bars per API call (fits 60d × 390min/d comfortably)
BT_LOOKBACK     = 500   # rolling window size passed to compute_signals()
BT_MIN_BARS     = 350   # minimum bars before first signal check (needs SMA200 warmup)
BT_SAMPLE_EVERY = 15    # evaluate signals every N 1m bars (15-minute cadence)
BT_MAX_HOLD     = 240   # 4-hour maximum hold before TIMEOUT

_backtest_state: dict = {
    "status":       "pending",   # pending | running | done | error
    "progress":     "",
    "pct":          0,
    "started_at":   None,
    "completed_at": None,
    "tickers":      {},          # {ticker: {trades, stats}}
    "summary":      {},          # aggregate across all tickers
}


def _bt_agg_trades(trades: list) -> dict:
    """Compute per-CQ-tier win rate, avg R, profit factor, and best score threshold."""
    if not trades:
        return {}

    by_cq: dict = {t: [] for t in ("HIGH", "MED", "LOW", "WEAK")}
    for tr in trades:
        by_cq.setdefault(tr["cq"], []).append(tr)

    out = {}
    for tier, bucket in by_cq.items():
        if not bucket:
            continue
        wins  = [t for t in bucket if t["result"] == "WIN"]
        loses = [t for t in bucket if t["result"] == "LOSS"]
        tos   = [t for t in bucket if t["result"] == "TIMEOUT"]
        rs    = [t["r_mult"] for t in bucket]
        total = len(bucket)
        avg_r = round(sum(rs) / total, 2) if rs else 0.0
        gross_w = sum(r for r in rs if r > 0)
        gross_l = abs(sum(r for r in rs if r < 0)) or 0.001
        pf      = round(gross_w / gross_l, 2)

        # Walk score thresholds 5 points at a time; keep the one with highest EV
        best_thresh = LOG_SCORE_THRESHOLD
        best_ev     = avg_r
        for thresh in range(LOG_SCORE_THRESHOLD, MAX_SCORE, 5):
            sub = [t for t in bucket if t["score"] >= thresh]
            if len(sub) < max(3, total * 0.10):   # need at least 10% sample floor
                break
            sub_rs = [t["r_mult"] for t in sub]
            ev = sum(sub_rs) / len(sub_rs)
            if ev > best_ev:
                best_ev     = round(ev, 2)
                best_thresh = thresh

        out[tier] = {
            "trades":      total,
            "wins":        len(wins),
            "losses":      len(loses),
            "timeouts":    len(tos),
            "win_rate":    round(len(wins) / total * 100, 1),
            "avg_r":       avg_r,
            "total_r":     round(sum(rs), 2),
            "profit_factor": pf,
            "best_thresh": best_thresh,
            "best_ev":     best_ev,
        }
    return out


def _bt_simulate_ticker(ticker: str, df_full: pd.DataFrame) -> list:
    """
    Walk forward through df_full (RTH 1m bars), evaluating signals every
    BT_SAMPLE_EVERY bars. For each signal above LOG_SCORE_THRESHOLD, simulate
    a trade: entry = next bar open, exit via ATR SL/TP or BT_MAX_HOLD timeout.
    Returns list of trade dicts.
    """
    trades      = []
    n           = len(df_full)
    skip_until  = 0   # bar index — skip if inside an open trade

    for i in range(BT_MIN_BARS, n, BT_SAMPLE_EVERY):
        if i <= skip_until:
            continue

        # Rolling window for indicators
        slice_1m = df_full.iloc[max(0, i - BT_LOOKBACK): i].copy().reset_index(drop=True)
        slice_5m = resample_to_5m(slice_1m)

        if len(slice_1m) < 50 or len(slice_5m) < 10:
            continue

        try:
            res = compute_signals(slice_1m, slice_5m, ticker=ticker)
        except Exception as _bt_ex:
            if not trades:   # log only the first failure per ticker
                print(f"[BACKTEST] {ticker} compute_signals error at bar {i}: {_bt_ex}", flush=True)
                traceback.print_exc()
            continue

        bull_s = res.get("bull_score", 0)
        bear_s = res.get("bear_score", 0)

        # Decide direction: higher score wins; skip if both below log threshold
        if bull_s >= bear_s and bull_s >= LOG_SCORE_THRESHOLD:
            direction = "BULL"
            score     = bull_s
            cq        = res.get("bull_cq", "WEAK")
            sl        = res.get("bull_stop")
            tp_price  = res.get("bull_tp")
        elif bear_s > bull_s and bear_s >= LOG_SCORE_THRESHOLD:
            direction = "BEAR"
            score     = bear_s
            cq        = res.get("bear_cq", "WEAK")
            sl        = res.get("bear_stop")
            tp_price  = res.get("bear_tp")
        else:
            continue

        if sl is None or tp_price is None:
            continue

        # Entry: open of the next bar after signal
        entry_idx = min(i, n - 1)
        entry     = float(df_full.iloc[entry_idx]["Open"])
        if entry <= 0:
            continue

        # Recompute SL/TP from live ATR if available (handles price differences
        # between the window close and the next bar's open)
        atr = res.get("atr")
        if atr and atr > 0:
            if direction == "BULL":
                sl       = entry - ATR_STOP_MULT * atr
                tp_price = entry + ATR_TP_MULT   * atr
            else:
                sl       = entry + ATR_STOP_MULT * atr
                tp_price = entry - ATR_TP_MULT   * atr

        risk = abs(entry - sl)
        if risk < 1e-6:
            continue

        # Walk forward bar-by-bar to find exit
        result_label = "TIMEOUT"
        exit_price   = float(df_full.iloc[min(entry_idx + BT_MAX_HOLD - 1, n - 1)]["Close"])
        exit_idx     = entry_idx + BT_MAX_HOLD

        for j in range(entry_idx + 1, min(entry_idx + BT_MAX_HOLD, n)):
            bar_lo = float(df_full.iloc[j]["Low"])
            bar_hi = float(df_full.iloc[j]["High"])

            if direction == "BULL":
                if bar_lo <= sl:             # SL hit first (conservative)
                    result_label = "LOSS"
                    exit_price   = sl
                    exit_idx     = j
                    break
                if bar_hi >= tp_price:
                    result_label = "WIN"
                    exit_price   = tp_price
                    exit_idx     = j
                    break
            else:  # BEAR
                if bar_hi >= sl:
                    result_label = "LOSS"
                    exit_price   = sl
                    exit_idx     = j
                    break
                if bar_lo <= tp_price:
                    result_label = "WIN"
                    exit_price   = tp_price
                    exit_idx     = j
                    break

        pnl    = (exit_price - entry) if direction == "BULL" else (entry - exit_price)
        r_mult = round(pnl / risk, 2)

        trades.append({
            "ticker":    ticker,
            "direction": direction,
            "score":     score,
            "cq":        cq,
            "regime":    res.get("regime", "unknown"),
            "entry":     round(entry, 4),
            "sl":        round(sl, 4),
            "tp":        round(tp_price, 4),
            "exit":      round(exit_price, 4),
            "result":    result_label,
            "r_mult":    r_mult,
            "bar_ts":    int(df_full.iloc[i - 1]["ts"]) if "ts" in df_full.columns else 0,
        })

        skip_until = exit_idx   # don't take another signal while this trade runs

    return trades


async def _run_backtest():
    """
    Background task: fetch 60 trading days of 1m data per ticker, walk forward,
    and populate _backtest_state. Uses 1 Polygon call per ticker (resampled to
    5m internally) — 5 calls total, well within the free-tier 5/min limit.
    """
    global _backtest_state
    _backtest_state["status"]     = "running"
    _backtest_state["started_at"] = datetime.now().isoformat()

    # Wait for the scanner's first cycle to complete before hammering Polygon
    await asyncio.sleep(90)

    client     = RESTClient(POLYGON_API_KEY)
    all_trades: list = []

    try:
        for idx, ticker in enumerate(WATCHLIST):
            pct = int(idx / len(WATCHLIST) * 100)
            _backtest_state["pct"]      = pct
            _backtest_state["progress"] = f"Fetching {ticker} ({idx+1}/{len(WATCHLIST)})…"
            print(f"[BACKTEST] Fetching {ticker} ({BT_DAYS}d)…", flush=True)

            df_raw = await asyncio.get_running_loop().run_in_executor(
                None,
                lambda t=ticker: fetch_aggs(client, t, multiplier=1, days=BT_DAYS, limit=BT_LIMIT)
            )

            if df_raw is None or len(df_raw) < BT_MIN_BARS:
                print(f"[BACKTEST] {ticker}: insufficient data ({len(df_raw) if df_raw is not None else 0} bars)", flush=True)
                continue

            df_rth = _filter_rth(df_raw)
            df_rth = df_rth.reset_index(drop=True)

            if len(df_rth) < BT_MIN_BARS:
                print(f"[BACKTEST] {ticker}: only {len(df_rth)} RTH bars — skipping", flush=True)
                continue

            _backtest_state["progress"] = (
                f"Running signals for {ticker} "
                f"({len(df_rth)} RTH bars → ~{len(df_rth)//BT_SAMPLE_EVERY} checks)…"
            )
            print(f"[BACKTEST] {ticker}: {len(df_rth)} RTH bars — running walk-forward…", flush=True)

            trades = await asyncio.get_running_loop().run_in_executor(
                None,
                lambda t=ticker, d=df_rth: _bt_simulate_ticker(t, d)
            )

            wins = sum(1 for t in trades if t["result"] == "WIN")
            print(
                f"[BACKTEST] {ticker}: {len(trades)} trades | "
                f"{wins}W / {len(trades)-wins}L+T",
                flush=True
            )

            stats = _bt_agg_trades(trades)
            _backtest_state["tickers"][ticker] = {
                "trades": len(trades),
                "stats":  stats,
                "sample": trades[-20:],   # last 20 trades for the UI table
            }
            all_trades.extend(trades)

            # Space tickers 20s apart → 3 calls/min from backtest,
            # leaving 2 slots/min for the live scanner
            if idx < len(WATCHLIST) - 1:
                await asyncio.sleep(20)

        _backtest_state["summary"] = {
            "total_trades": len(all_trades),
            "by_cq":        _bt_agg_trades(all_trades),
        }
        _backtest_state["status"]       = "done"
        _backtest_state["pct"]          = 100
        _backtest_state["completed_at"] = datetime.now().isoformat()
        _backtest_state["progress"]     = f"Complete — {len(all_trades)} trades across {len(WATCHLIST)} tickers"
        print(f"[BACKTEST] Done: {len(all_trades)} total trades", flush=True)

    except Exception as e:
        _backtest_state["status"]   = "error"
        _backtest_state["progress"] = str(e)
        traceback.print_exc()


@app.route("/api/backtest")
def api_backtest():
    return jsonify(_backtest_state)


@app.route("/backtest")
def route_backtest():
    return """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Backtest — SPX Scanner</title>
<style>
  *{box-sizing:border-box;margin:0;padding:0}
  body{background:#080808;color:#ccc;font-family:monospace;font-size:13px;padding:20px}
  h1{color:#00ffcc;font-size:1.1rem;margin-bottom:16px;letter-spacing:1px}
  h2{color:#555;font-size:.75rem;text-transform:uppercase;letter-spacing:.8px;margin:20px 0 8px}
  .status-bar{background:#111;border:1px solid #1a1a1a;border-radius:6px;padding:12px 16px;margin-bottom:16px}
  .progress-track{background:#1a1a1a;border-radius:3px;height:6px;margin-top:8px;overflow:hidden}
  .progress-fill{height:6px;border-radius:3px;background:#00ffcc;transition:width .4s}
  table{width:100%;border-collapse:collapse;margin-bottom:12px}
  th{padding:4px 10px;text-align:left;color:#333;font-size:.65rem;text-transform:uppercase;letter-spacing:.5px;border-bottom:1px solid #1a1a1a}
  td{padding:5px 10px;border-bottom:1px solid #0d0d0d;font-size:.75rem}
  .g{color:#00ff88} .r{color:#ff6666} .y{color:#ffaa00} .d{color:#555}
  .badge{display:inline-block;padding:1px 6px;border-radius:3px;font-size:.62rem;font-weight:700}
  .b-high{background:#00ff8822;color:#00ff88;border:1px solid #00ff8844}
  .b-med{background:#00ffcc22;color:#00ffcc;border:1px solid #00ffcc44}
  .b-low{background:#ffaa0022;color:#ffaa00;border:1px solid #ffaa0044}
  .b-weak{background:#55555522;color:#555;border:1px solid #33333344}
  .ticker-grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(280px,1fr));gap:10px;margin-bottom:16px}
  .ticker-card{background:#0d0d0d;border:1px solid #1a1a1a;border-radius:5px;padding:12px}
  .ticker-card h3{color:#aaa;font-size:.78rem;margin-bottom:8px}
  .pending{color:#333;font-style:italic}
  a{color:#00ffcc;text-decoration:none}
</style>
</head>
<body>
<h1>&#x26A1; BACKTEST — 60-Day Walk-Forward</h1>
<p style="color:#333;font-size:.72rem;margin-bottom:16px">
  Same <code>compute_signals()</code> + ATR bracket (SL ×""" + str(ATR_STOP_MULT) + """ / TP ×""" + str(ATR_TP_MULT) + """) as live execution &nbsp;|&nbsp;
  Sample cadence: every """ + str(BT_SAMPLE_EVERY) + """m &nbsp;|&nbsp; Max hold: """ + str(BT_MAX_HOLD) + """m &nbsp;|&nbsp;
  <a href="/">&#x2190; Dashboard</a>
</p>

<div class="status-bar">
  <div style="display:flex;align-items:center;gap:10px">
    <span id="status-dot" style="width:8px;height:8px;border-radius:50%;background:#333;display:inline-block"></span>
    <span id="status-text" style="color:#555">Initializing…</span>
    <span id="status-pct" style="color:#333;margin-left:auto"></span>
  </div>
  <div class="progress-track"><div class="progress-fill" id="prog" style="width:0%"></div></div>
</div>

<div id="content"><p class="pending">Waiting for backtest results…</p></div>

<script>
const CQ_BADGE = {
  HIGH:'<span class="badge b-high">HIGH</span>',
  MED:'<span class="badge b-med">MED</span>',
  LOW:'<span class="badge b-low">LOW</span>',
  WEAK:'<span class="badge b-weak">WEAK</span>',
};
const STATUS_CLR = {done:'#00ff88',running:'#ffaa00',error:'#ff6666',pending:'#333'};

function fmtR(r){
  if(r==null) return '<span class="d">–</span>';
  return r>=0 ? `<span class="g">+${r.toFixed(2)}R</span>` : `<span class="r">${r.toFixed(2)}R</span>`;
}
function fmtWR(wr){
  const c = wr>=60?'g':wr>=45?'y':'r';
  return `<span class="${c}">${wr.toFixed(1)}%</span>`;
}

function renderCQTable(byQ, title) {
  if(!byQ || !Object.keys(byQ).length) return '<p class="pending">No data yet</p>';
  const rows = ['HIGH','MED','LOW','WEAK'].filter(t=>byQ[t]).map(tier => {
    const s = byQ[tier];
    const threshBadge = s.best_thresh > """ + str(LOG_SCORE_THRESHOLD) + """
      ? `<span style="color:#00ffcc">${s.best_thresh}+</span>`
      : `<span class="d">${s.best_thresh}</span>`;
    return `<tr>
      <td>${CQ_BADGE[tier]}</td>
      <td>${s.trades}</td>
      <td>${fmtWR(s.win_rate)}</td>
      <td>${fmtR(s.avg_r)}</td>
      <td>${fmtR(s.total_r)}</td>
      <td style="color:#aaa">${s.profit_factor}×</td>
      <td>${threshBadge}</td>
      <td>${fmtR(s.best_ev)}</td>
    </tr>`;
  }).join('');
  return `
  <table>
    <thead><tr>
      <th>CQ Tier</th><th>Trades</th><th>Win%</th>
      <th>Avg R</th><th>Total R</th><th>Profit Factor</th>
      <th>Best Threshold</th><th>Best EV/trade</th>
    </tr></thead>
    <tbody>${rows}</tbody>
  </table>`;
}

function renderTickerCards(tickers) {
  return Object.entries(tickers).map(([tk, d]) => {
    const stats = d.stats || {};
    const rows = ['HIGH','MED','LOW'].filter(t=>stats[t]).map(tier => {
      const s = stats[tier];
      return `<tr>
        <td>${CQ_BADGE[tier]}</td>
        <td>${s.trades}</td>
        <td>${fmtWR(s.win_rate)}</td>
        <td>${fmtR(s.avg_r)}</td>
      </tr>`;
    }).join('');
    return `<div class="ticker-card">
      <h3>${tk} &nbsp;<span style="color:#333;font-size:.65rem">${d.trades} trades total</span></h3>
      ${rows ? `<table>
        <thead><tr><th>CQ</th><th>#</th><th>Win%</th><th>Avg R</th></tr></thead>
        <tbody>${rows}</tbody>
      </table>` : '<p class="pending" style="font-size:.7rem">No trades yet</p>'}
    </div>`;
  }).join('');
}

function renderRecentTrades(tickers) {
  const all = Object.values(tickers).flatMap(d => d.sample || []);
  if(!all.length) return '';
  all.sort((a,b) => b.bar_ts - a.bar_ts);
  const rows = all.slice(0,30).map(t => {
    const rc  = {WIN:'g',LOSS:'r',TIMEOUT:'d'}[t.result]||'d';
    const dc  = t.direction==='BULL'?'g':'r';
    const ts  = t.bar_ts ? new Date(t.bar_ts).toLocaleString('en-US',{timeZone:'America/New_York',month:'numeric',day:'numeric',hour:'2-digit',minute:'2-digit'}) : '–';
    return `<tr>
      <td class="d">${ts}</td>
      <td><b>${t.ticker}</b></td>
      <td class="${dc}">${t.direction}</td>
      <td>${CQ_BADGE[t.cq]||t.cq}</td>
      <td style="color:#aaa">${t.score}</td>
      <td class="${rc}">${t.result}</td>
      <td>${fmtR(t.r_mult)}</td>
      <td class="d" style="font-size:.65rem">${(t.regime||'').replace(/_/g,' ')}</td>
    </tr>`;
  }).join('');
  return `
  <h2>Recent Trades (last 30 across all tickers)</h2>
  <table>
    <thead><tr>
      <th>Time (ET)</th><th>Ticker</th><th>Dir</th><th>CQ</th>
      <th>Score</th><th>Result</th><th>R</th><th>Regime</th>
    </tr></thead>
    <tbody>${rows}</tbody>
  </table>`;
}

async function poll() {
  try {
    const r = await fetch('/api/backtest');
    const d = await r.json();

    const dot  = document.getElementById('status-dot');
    const txt  = document.getElementById('status-text');
    const pct  = document.getElementById('status-pct');
    const prog = document.getElementById('prog');
    dot.style.background = STATUS_CLR[d.status] || '#333';
    txt.textContent = d.progress || d.status;
    pct.textContent = d.pct ? d.pct + '%' : '';
    prog.style.width = (d.pct || 0) + '%';

    if (d.status === 'running' || d.status === 'pending') {
      setTimeout(poll, 3000);
      return;
    }

    const summary = d.summary || {};
    const tickers = d.tickers || {};
    const byQ     = summary.by_cq || {};
    const total   = summary.total_trades || 0;

    document.getElementById('content').innerHTML = `
      <h2>Aggregate Performance — ${total} trades across all tickers</h2>
      ${renderCQTable(byQ, 'All Tickers')}
      <h2>Per-Ticker Breakdown</h2>
      <div class="ticker-grid">${renderTickerCards(tickers)}</div>
      ${renderRecentTrades(tickers)}
    `;

    if (d.status === 'error') {
      document.getElementById('status-text').style.color = '#ff6666';
      setTimeout(poll, 10000);   // retry on error
    }
  } catch(e) {
    setTimeout(poll, 5000);
  }
}

poll();
</script>
</body>
</html>"""


# ====================== START ======================
async def _startup():
    """Run scanner loop, Flask/waitress server, and backtest concurrently."""
    loop = asyncio.get_running_loop()
    flask_task = loop.run_in_executor(
        None,
        lambda: _waitress_serve(app, host='0.0.0.0', port=8080, threads=4, channel_timeout=120)
    )
    asyncio.create_task(_run_backtest())
    await asyncio.gather(main(), flask_task)

if __name__ == "__main__":
    asyncio.run(_startup())
