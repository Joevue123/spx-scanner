import asyncio
import csv
import itertools
import json
import math
import os
import smtplib
import threading
import traceback
from datetime import datetime, date, timedelta, timezone
from email.mime.text import MIMEText

import pandas as pd
import pandas_ta as ta
import requests
from flask import Flask, jsonify
from polygon import RESTClient

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
MAX_SCORE             = 17       # 16 Phase-1 + VIX alignment (1pt per direction)
ALERT_COOLDOWN_SECS   = 900
VOLUME_SPIKE_MULT     = 3.0
ALERT_SCORE_THRESHOLD = 9
LOG_SCORE_THRESHOLD   = 6
ATR_STOP_MULT         = 1.5      # stop loss = price ± 1.5×ATR
ATR_TP_MULT           = 2.5      # take profit = price ± 2.5×ATR
ACCOUNT_SIZE          = float(os.getenv("ACCOUNT_SIZE", "25000"))
RISK_PCT              = 0.01     # risk 1% of account per trade
BREADTH_BULL_THRESH   = 3   # tickers in BULL needed for "bull dominant" breadth
BREADTH_BEAR_THRESH   = 3   # tickers in BEAR needed for "bear dominant" breadth

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
                       volume_spike=False, atr=None, stop=None, tp=None):
    global _last_alert_times
    now  = datetime.now()
    last = _last_alert_times.get(ticker)
    if last and (now - last).total_seconds() < ALERT_COOLDOWN_SECS:
        remaining = int(ALERT_COOLDOWN_SECS - (now - last).total_seconds())
        print(f"Alert suppressed [{ticker}] — cooldown {remaining}s", flush=True)
        return

    score = bull_score if direction == "BULL" else bear_score
    arrow = "🔥" if direction == "BULL" else "🔻"
    vol   = " ⚡ VOLUME SPIKE" if volume_spike else ""
    levels = ""
    if atr and stop and tp:
        levels = f"\nATR: {atr:.2f} | SL: ${stop:.2f} | TP: ${tp:.2f}"

    msg = (
        f"{arrow} *{ticker} {direction} Confluence Alert*{vol}\n"
        f"Price: ${price:.2f} | Score: {score}/{MAX_SCORE}"
        f"{levels}\n"
        f"Time: {now.strftime('%H:%M:%S ET')}"
    )

    _send_discord(ticker, msg)
    _send_telegram(msg)
    _send_email(
        subject=f"[Scanner] {ticker} {direction} — {score}/{MAX_SCORE}{vol}",
        body=msg.replace("*", "").replace("🔥", "").replace("🔻", "").replace("⚡", "")
    )

    _last_alert_times[ticker] = now

    dashboard_data[ticker]["alerts"].insert(0, {
        "time":      now.strftime("%H:%M:%S"),
        "price":     round(float(price), 2),
        "score":     score,
        "direction": direction,
        "message":   f"{direction} confluence{vol}",
    })
    dashboard_data[ticker]["alerts"] = dashboard_data[ticker]["alerts"][:10]


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
    "bull_signals": {},
    "bear_signals": {},
    "history":      load_history(t),
    "alerts":       [],
}

dashboard_data = {t: _blank_ticker(t) for t in WATCHLIST}
signal_log     = load_signal_log()

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
        "tickers":     dashboard_data,
        "signal_log":  signal_log[-50:],
        "market_open": is_market_open(),
        "vix":         vix_data,
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


def compute_signals(df_1m, df_5m):
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

    # ── 5m indicators ─────────────────────────────────────────────────────────
    df5 = df_5m.copy()
    df5['sma20'] = ta.sma(df5['Close'], length=20)
    df5['rsi']   = ta.rsi(df5['Close'], length=14)
    st5_df       = ta.supertrend(df5['High'], df5['Low'], df5['Close'], length=7, multiplier=1.0)
    df5['st']    = st5_df.iloc[:, 0]
    df5 = df5.bfill()

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

    # ── Snapshot values ───────────────────────────────────────────────────────
    price    = float(df['Close'].iloc[-1])
    sma20_1m = float(df['sma20'].iloc[-1])
    rsi_1m   = float(df['rsi'].iloc[-1])
    adx_val  = float(df['adx'].iloc[-1])
    dmp_val  = float(df['dmp'].iloc[-1])
    dmn_val  = float(df['dmn'].iloc[-1])
    st_1m    = float(df['st'].iloc[-1])
    sma20_5m = float(df5['sma20'].iloc[-1])
    st_5m    = float(df5['st'].iloc[-1])
    price_5m = float(df5['Close'].iloc[-1])

    ha_bull_1m = _calc_ha_bull(df)
    ha_bull_5m = _calc_ha_bull(df5)
    ftfc_1m    = float((df['Close']  > df['Open']).tail(30).mean())
    ftfc_5m    = float((df5['Close'] > df5['Open']).tail(30).mean())
    fvg_dir    = detect_fvg(df)
    ob_dir     = detect_order_blocks(df)
    rsi_div    = detect_rsi_divergence(df)

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

    # ── Signal builder helper ──────────────────────────────────────────────────
    def bs(label, pts, active, value, tf1=None, tf5=None):
        d = {"label": label, "points": pts, "active": bool(active), "value": value}
        if tf1 is not None: d["tf1"] = bool(tf1)
        if tf5 is not None: d["tf5"] = bool(tf5)
        return d

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

    bull = {
        "sma20":       bs("SMA20 MTF",      2, sma_b1 and sma_b5,      f"{sma20_1m:.2f}" if _valid(sma20_1m) else "--",  sma_b1, sma_b5),
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
        "orb":         bs("ORB Break ↑",     1, orb_dir == 'bull',      f">{orb_high:.2f}" if orb_high else "No ORB"),
        "gap":         bs("Gap Up",          1, gap_dir == 'bull',      f"+{gap_pct:.2f}%" if (gap_pct is not None and gap_pct > 0) else (f"{gap_pct:.2f}%" if gap_pct is not None else "--")),
        "vix":         bs("Breadth Bull",     1, vix_bull,               vix_label),
    }
    bull_score = sum(s['points'] for s in bull.values() if s['active'])

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
        "orb":         bs("ORB Break ↓",      1, orb_dir == 'bear',     f"<{orb_low:.2f}" if orb_low else "No ORB"),
        "gap":         bs("Gap Down",         1, gap_dir == 'bear',     f"{gap_pct:.2f}%" if (gap_pct is not None and gap_pct < 0) else (f"+{gap_pct:.2f}%" if gap_pct is not None else "--")),
        "vix":         bs("Breadth Bear",     1, vix_bear,               vix_label),
    }
    bear_score = sum(s['points'] for s in bear.values() if s['active'])

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
    }


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


async def scan_ticker(client, ticker, market_open):
    print(f"Scanning {ticker}...", flush=True)

    # Fetch ~5 trading days of 1m bars (2000 > 5×390 RTH bars/day)
    df_raw = fetch_aggs(client, ticker, multiplier=1, days=7, limit=2000)
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

    # ── Pre-market gap: compare today's pre-market bars to yesterday RTH close ─
    pm_gap_pct = None
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
    except Exception:
        pass

    result    = compute_signals(df_1m, df_5m)
    price     = result['price']
    bull_score= result['bull_score']
    bear_score= result['bear_score']
    direction = result['direction']
    vol_spike = result['volume_spike']
    score     = bull_score if direction != "BEAR" else bear_score

    if not market_open:
        status = "MARKET_CLOSED"
    elif score >= 8:
        status = "NORMAL"
    else:
        status = "REDUCED_RISK"

    # History (once per minute)
    history = dashboard_data[ticker]["history"]
    current_minute = datetime.now().strftime("%H:%M")
    if not history or history[-1]["time"] != current_minute:
        history.append({"time": current_minute, "bull_score": int(bull_score), "bear_score": int(bear_score)})
        if len(history) > 60:
            history.pop(0)
        save_history(ticker, history)

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
        "bull_signals": result['bull_signals'],
        "bear_signals": result['bear_signals'],
        "history":      history,
    })

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
        }
        signal_log.insert(0, entry)
        signal_log = signal_log[:200]
        save_signal_log(signal_log)
        log_to_csv(entry)

    # External alerts
    if market_open and score >= ALERT_SCORE_THRESHOLD:
        stop = result['bull_stop'] if direction != "BEAR" else result['bear_stop']
        tp   = result['bull_tp']   if direction != "BEAR" else result['bear_tp']
        send_notifications(ticker, price, bull_score, bear_score, direction,
                           vol_spike, result['atr'], stop, tp)

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

    client = RESTClient(POLYGON_API_KEY)
    print(f"Watchlist: {', '.join(WATCHLIST)}", flush=True)

    while True:
        try:
            market_open = is_market_open()
            for ticker in WATCHLIST:
                try:
                    await scan_ticker(client, ticker, market_open)
                except Exception:
                    print(f"Error scanning {ticker}:", flush=True)
                    traceback.print_exc()
                await asyncio.sleep(1)
            # Compute breadth from this cycle's results (no extra API call)
            update_market_breadth()
        except Exception:
            traceback.print_exc()

        await asyncio.sleep(300 if not is_market_open() else 45)


# ====================== DASHBOARD HTML ======================

DASHBOARD_HTML = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
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
    .tcrd{padding:9px 10px}
    .tcrd .t-price{font-size:1.1rem}
    h1{font-size:1.1rem}
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
  </div>

  <!-- Ticker Summary Row -->
  <div class="row g-2 mb-3" id="ticker-row"></div>

  <!-- Detail Panel -->
  <div class="card p-3 mb-3">
    <!-- Tab bar -->
    <div class="d-flex align-items-center gap-2 mb-2 flex-wrap">
      <div class="section-title mb-0" id="detail-title">SPY — Signals</div>
      <div class="d-flex gap-1">
        <button class="tab-btn active" id="tab-bull" onclick="setDir('bull')">🔼 Bull</button>
        <button class="tab-btn"        id="tab-bear" onclick="setDir('bear')">🔽 Bear</button>
      </div>
      <span id="vol-spike-badge" class="vol-spike d-none">⚡ VOL SPIKE</span>
    </div>

    <!-- Context row: Gap + ORB -->
    <div id="ctx-row" class="mb-2"></div>

    <!-- Signal Grid -->
    <div class="row g-2 mb-3" id="signal-grid"></div>

    <!-- ATR Risk Panel -->
    <div>
      <div class="section-title">ATR Risk Levels</div>
      <div id="risk-panel" class="d-flex flex-wrap gap-1"></div>
    </div>
  </div>

  <!-- Charts + Alerts Row -->
  <div class="row g-3 mb-3">
    <div class="col-md-5">
      <div class="card p-3">
        <div class="section-title">Score History — <span id="chart-ticker">SPY</span></div>
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
        <div class="section-title mt-2">VIX (CBOE)</div>
        <iframe
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
          <th>Bull</th><th>Bear</th><th>Dir</th>
          <th>ATR</th><th>Stop</th><th>TP</th><th>Gap</th><th>Vol</th>
        </tr></thead>
        <tbody id="log-body">
          <tr><td colspan="11" style="color:#555;text-align:center;padding:12px">No setups logged yet</td></tr>
        </tbody>
      </table>
    </div>
  </div>

</div>

<script>
let allData    = {};
let signalLog  = [];
let vixData    = null;
let curTicker  = 'SPY';
let curDir     = 'bull';
let soundOn    = true;
let prevScores = {};
let scoreChart = null;

const MAX_SCORE = """ + str(MAX_SCORE) + """;

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

// ── Ticker summary cards ──────────────────────────────────────────────────────
function renderTickerRow() {
  const row = document.getElementById('ticker-row');
  row.innerHTML = '';
  for (const ticker of Object.keys(allData)) {
    const d = allData[ticker];
    const score  = d.direction === 'BEAR' ? d.bear_score : d.bull_score;
    const dirCls = {BULL:'dir-bull',BEAR:'dir-bear',NEUTRAL:'dir-neutral'}[d.direction] || 'dir-starting';
    const gapHtml = d.gap_pct != null
      ? `<span class="ctx-badge ${d.gap_pct>0?'ctx-bull':d.gap_pct<0?'ctx-bear':'ctx-neutral'}">${d.gap_pct>0?'+':''}${d.gap_pct.toFixed(2)}%</span>`
      : '';
    const col = document.createElement('div');
    col.className = 'col-6 col-sm-4 col-md-3 col-xl-2';
    col.innerHTML = `
      <div class="tcrd${ticker===curTicker?' active':''}" onclick="selectTicker('${ticker}')">
        <div class="d-flex justify-content-between align-items-start">
          <span class="t-ticker">${ticker}</span>
          <span class="t-dir ${dirCls}">${d.direction}</span>
        </div>
        <div class="t-price">$${d.price.toFixed(2)}</div>
        <div class="t-score d-flex align-items-center gap-1 flex-wrap">
          <span style="color:#00ff88">▲${d.bull_score}</span>
          <span style="color:#ff6666">▼${d.bear_score}</span>
          <span style="color:#444">/${MAX_SCORE}</span>
          ${gapHtml}
          ${d.volume_spike?'<span class="vol-spike" style="padding:1px 5px">⚡</span>':''}
        </div>
        <div class="bar-wrap mt-1">
          <div class="bar" style="width:${Math.min(score/MAX_SCORE*100,100)}%;background:${scoreColor(score)}"></div>
        </div>
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

// ── Direction tabs ────────────────────────────────────────────────────────────
function setDir(dir) {
  curDir = dir;
  document.getElementById('tab-bull').className = 'tab-btn' + (dir==='bull'?' active':'');
  document.getElementById('tab-bear').className = 'tab-btn' + (dir==='bear'?' active':'');
  renderSignals();
  renderRiskPanel();
}

// ── Context row (Gap + ORB + Pre-market Gap) ─────────────────────────────────
function renderContextRow() {
  const d = allData[curTicker];
  if (!d) return;
  const row = document.getElementById('ctx-row');
  let html = '';

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

  row.innerHTML = html;
}

// ── Signal grid ───────────────────────────────────────────────────────────────
function renderSignals() {
  const d = allData[curTicker];
  if (!d) return;
  const signals = curDir === 'bull' ? d.bull_signals : d.bear_signals;
  const grid = document.getElementById('signal-grid');
  grid.innerHTML = '';
  for (const [, sig] of Object.entries(signals || {})) {
    const col = document.createElement('div');
    col.className = 'col-6 col-md-4 col-xl-3';
    const tfHtml = sig.tf1 !== undefined
      ? `<span class="tf-badge ${sig.tf1?'tf-ok':'tf-no'}">1m</span><span class="tf-badge ${sig.tf5?'tf-ok':'tf-no'}">5m</span>`
      : '';
    const color = sig.active ? (curDir==='bull'?'#00ff88':'#ff6666') : '#444';
    col.innerHTML = `<div class="sig-card ${sig.active?'active':'inactive'}">
      <span class="sig-icon">${sig.active?(curDir==='bull'?'✅':'🔴'):'❌'}</span>
      <div class="sig-label">${sig.label} ${tfHtml} <small style="color:#444">${sig.points}pt</small></div>
      <div class="sig-val" style="color:${color}">${sig.value}</div>
    </div>`;
    grid.appendChild(col);
  }

  const vsBadge = document.getElementById('vol-spike-badge');
  const d2 = allData[curTicker];
  if (d2 && d2.volume_spike) {
    vsBadge.classList.remove('d-none');
    vsBadge.textContent = '⚡ VOL SPIKE ' + (d2.vol_ratio ? d2.vol_ratio+'x' : '');
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
    const clr = a.direction==='BULL' ? '#00ff88' : '#ff6666';
    return `<div class="alert-item">
      <span style="color:#ffaa00">${a.time}</span>
      <span class="ms-2 fw-bold" style="color:${clr}">${a.direction}</span>
      <span class="ms-2">$${a.price.toFixed(2)}</span>
      <span class="ms-1 text-muted">· ${a.score}pts</span>
      <div style="color:#777;font-size:.7rem;margin-top:2px">${a.message}</div>
    </div>`;
  }).join('');
}

// ── Score Chart ───────────────────────────────────────────────────────────────
function initChart() {
  const ctx = document.getElementById('scoreChart').getContext('2d');
  scoreChart = new Chart(ctx, {
    type: 'line',
    data: {
      labels: [],
      datasets: [
        {label:'Bull',data:[],borderColor:'#00ff88',backgroundColor:'rgba(0,255,136,.06)',tension:.3,pointRadius:2,fill:true},
        {label:'Bear',data:[],borderColor:'#ff6666',backgroundColor:'rgba(255,100,100,.05)',tension:.3,pointRadius:2,fill:true}
      ]
    },
    options: {
      responsive:true, animation:{duration:250},
      interaction:{mode:'index',intersect:false},
      scales:{
        x:{ticks:{color:'#444',maxTicksLimit:8,font:{size:9}}, grid:{color:'#1a1a1a'}},
        y:{min:0,max:MAX_SCORE,ticks:{color:'#444',stepSize:2},grid:{color:'#1a1a1a'}}
      },
      plugins:{legend:{labels:{color:'#555',font:{size:10}}}}
    }
  });
}

function updateChart() {
  const d = allData[curTicker];
  if (!d || !d.history || d.history.length === 0 || !scoreChart) return;
  scoreChart.data.labels           = d.history.map(h => h.time);
  scoreChart.data.datasets[0].data = d.history.map(h => h.bull_score);
  scoreChart.data.datasets[1].data = d.history.map(h => h.bear_score);
  scoreChart.update('none');
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
    const res  = await fetch('/api/status');
    const data = await res.json();
    allData   = data.tickers    || {};
    signalLog = data.signal_log  || [];
    vixData   = data.vix         || null;

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
      if (newMax >= 8 && newMax > prevMax)
        playAlert(newMax >= 11 ? 1100 : 880, newMax >= 11 ? 3 : 2);
      prevScores[ticker] = {bull: d.bull_score, bear: d.bear_score};
      if (d.last_update !== 'N/A') latestUpdate = d.last_update;
    }
    document.getElementById('last-update').textContent = latestUpdate;

    renderTickerRow();
    renderSignals();
    renderRiskPanel();
    renderContextRow();
    renderAlerts();
    updateChart();
    renderLog();
  } catch(e) {
    console.error('Update error:', e);
  }
}

initChart();
update();
setInterval(update, 5000);
</script>
</body>
</html>"""

# ====================== START ======================
threading.Thread(
    target=lambda: asyncio.run(main()),
    daemon=True
).start()

if __name__ == "__main__":
    app.run(host='0.0.0.0', port=8080, debug=False)
