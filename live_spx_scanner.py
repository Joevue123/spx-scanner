import asyncio
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

WATCHLIST             = ["SPY", "QQQ", "IWM"]
SIGNAL_LOG_FILE       = "/tmp/signal_log.json"
HISTORY_FILE_TMPL     = "/tmp/score_history_{}.json"
MAX_SCORE             = 12       # max points per direction
ALERT_COOLDOWN_SECS   = 900      # 15 min between alerts per ticker
VOLUME_SPIKE_MULT     = 3.0      # x avg volume to trigger spike alert
ALERT_SCORE_THRESHOLD = 9        # send external notifications at this score
LOG_SCORE_THRESHOLD   = 6        # write to signal log at this score

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
    """
    Regular RSI divergence on last 30 bars.
    Bull: price lower low, RSI higher low.
    Bear: price higher high, RSI lower high.
    Returns 'bull', 'bear', or None.
    """
    try:
        if len(df) < 30 or 'rsi' not in df.columns:
            return None
        prices    = df['Close'].values[-30:]
        rsi_vals  = df['rsi'].values[-30:]
        half = 15
        prior_p, recent_p = prices[:half],    prices[half:]
        prior_r, recent_r = rsi_vals[:half],  rsi_vals[half:]

        pi_low  = prior_p.argmin();  ri_low  = recent_p.argmin()
        if recent_p[ri_low] < prior_p[pi_low] and recent_r[ri_low] > prior_r[pi_low]:
            return 'bull'

        pi_high = prior_p.argmax();  ri_high = recent_p.argmax()
        if recent_p[ri_high] > prior_p[pi_high] and recent_r[ri_high] < prior_r[pi_high]:
            return 'bear'

        return None
    except Exception:
        return None


# ====================== NOTIFICATIONS ======================

_last_alert_times = {}   # {ticker: datetime}


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


def send_notifications(ticker, price, bull_score, bear_score, direction, volume_spike=False):
    global _last_alert_times
    now = datetime.now()
    last = _last_alert_times.get(ticker)
    if last and (now - last).total_seconds() < ALERT_COOLDOWN_SECS:
        remaining = int(ALERT_COOLDOWN_SECS - (now - last).total_seconds())
        print(f"Alert suppressed [{ticker}] — cooldown {remaining}s", flush=True)
        return

    score = bull_score if direction == "BULL" else bear_score
    arrow = "🔥" if direction == "BULL" else "🔻"
    vol   = " ⚡ VOLUME SPIKE" if volume_spike else ""
    msg   = (
        f"{arrow} *{ticker} {direction} Confluence Alert*{vol}\n"
        f"Price: ${price:.2f} | Score: {score}/{MAX_SCORE}\n"
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

_blank_signals = lambda: {
    "sma20":       {"value": "--", "active": False, "label": "SMA20 MTF",     "points": 2, "dir": "bull"},
    "adx":         {"value": "--", "active": False, "label": "ADX",           "points": 1, "dir": "bull"},
    "rsi":         {"value": "--", "active": False, "label": "RSI",           "points": 1, "dir": "bull"},
    "ftfc":        {"value": "--", "active": False, "label": "FTFC MTF",      "points": 2, "dir": "bull"},
    "supertrend":  {"value": "--", "active": False, "label": "SuperTrend MTF","points": 1, "dir": "bull"},
    "heikin_ashi": {"value": "--", "active": False, "label": "Heikin Ashi MTF","points":1, "dir": "bull"},
    "vwap":        {"value": "--", "active": False, "label": "VWAP",          "points": 1, "dir": "bull"},
    "fvg":         {"value": "--", "active": False, "label": "FVG",           "points": 1, "dir": "bull"},
    "ob":          {"value": "--", "active": False, "label": "Order Block",   "points": 1, "dir": "bull"},
    "rsi_div":     {"value": "--", "active": False, "label": "RSI Divergence","points": 1, "dir": "bull"},
}

dashboard_data = {
    ticker: {
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
        "bull_signals": _blank_signals(),
        "bear_signals": _blank_signals(),
        "history":      load_history(ticker),
        "alerts":       [],
    }
    for ticker in WATCHLIST
}

signal_log = load_signal_log()

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
        "tickers":     list(dashboard_data.keys()),
        "time":        datetime.now().strftime("%H:%M:%S"),
    })


@app.route('/test-alert')
def test_alert():
    send_notifications("SPY", 500.0, 10, 2, "BULL", volume_spike=False)
    return jsonify({"status": "success"})


# ====================== SCANNER ======================


def resample_to_5m(df_1m):
    """Resample 1m OHLCV to 5m using pandas — avoids extra API calls."""
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
    """Fetch candles, return a DataFrame or None."""
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
    """
    Compute all bull and bear signals on 1m + 5m data.
    Returns a result dict.
    """
    # --- Indicators on 1m ---
    df = df_1m.copy()
    df['sma20']  = ta.sma(df['Close'], length=20)
    df['rsi']    = ta.rsi(df['Close'], length=14)
    adx_df       = ta.adx(df['High'], df['Low'], df['Close'], length=14)
    df['adx']    = adx_df.get('ADX_14', adx_df.iloc[:, 0])
    df['dmp']    = adx_df.get('DMP_14', adx_df.iloc[:, 1])
    df['dmn']    = adx_df.get('DMN_14', adx_df.iloc[:, 2])
    st_df        = ta.supertrend(df['High'], df['Low'], df['Close'], length=7, multiplier=1.0)
    df['st']     = st_df.iloc[:, 0]
    df = df.bfill()

    # --- Indicators on 5m ---
    df5 = df_5m.copy()
    df5['sma20'] = ta.sma(df5['Close'], length=20)
    df5['rsi']   = ta.rsi(df5['Close'], length=14)
    st5_df       = ta.supertrend(df5['High'], df5['Low'], df5['Close'], length=7, multiplier=1.0)
    df5['st']    = st5_df.iloc[:, 0]
    df5 = df5.bfill()

    # --- VWAP on today's 1m data ---
    last_day = df['date'].iloc[-1]
    day_df   = df[df['date'] == last_day].copy().reset_index(drop=True)
    vwap_val = None
    if len(day_df) >= 5:
        day_df.index = pd.to_datetime(
            day_df['ts'], unit='ms', utc=True
        ).dt.tz_convert('America/New_York')
        vwap_s = ta.vwap(day_df['High'], day_df['Low'], day_df['Close'], day_df['Volume'])
        if vwap_s is not None and len(vwap_s) > 0:
            vwap_val = vwap_s.iloc[-1]

    # --- Snapshot values ---
    price     = df['Close'].iloc[-1]
    sma20_1m  = df['sma20'].iloc[-1]
    rsi_1m    = df['rsi'].iloc[-1]
    adx_val   = df['adx'].iloc[-1]
    dmp_val   = df['dmp'].iloc[-1]
    dmn_val   = df['dmn'].iloc[-1]
    st_1m     = df['st'].iloc[-1]
    sma20_5m  = df5['sma20'].iloc[-1]
    st_5m     = df5['st'].iloc[-1]
    price_5m  = df5['Close'].iloc[-1]

    ha_bull_1m = _calc_ha_bull(df)
    ha_bull_5m = _calc_ha_bull(df5)
    ftfc_1m    = float((df['Close']  > df['Open']).tail(30).mean())
    ftfc_5m    = float((df5['Close'] > df5['Open']).tail(30).mean())
    fvg_dir    = detect_fvg(df)
    ob_dir     = detect_order_blocks(df)
    rsi_div    = detect_rsi_divergence(df)

    vol_avg    = df['Volume'].rolling(20).mean().iloc[-1]
    vol_cur    = df['Volume'].iloc[-1]
    vol_spike  = bool(_valid(vol_avg) and vol_avg > 0 and vol_cur > VOLUME_SPIKE_MULT * vol_avg)
    vol_ratio  = round(vol_cur / vol_avg, 1) if (_valid(vol_avg) and vol_avg > 0) else None

    # ---- Bull signals ----
    def bs(label, pts, active, value, tf1=None, tf5=None):
        d = {"label": label, "points": pts, "active": bool(active), "value": value}
        if tf1 is not None: d["tf1"] = bool(tf1)
        if tf5 is not None: d["tf5"] = bool(tf5)
        return d

    sma_b1 = _valid(sma20_1m) and price    > sma20_1m
    sma_b5 = _valid(sma20_5m) and price_5m > sma20_5m
    adx_b  = _valid(adx_val) and adx_val > 22 and _valid(dmp_val) and _valid(dmn_val) and dmp_val > dmn_val
    rsi_b  = _valid(rsi_1m)  and 45 < rsi_1m < 65
    ftfc_b1= _valid(ftfc_1m) and ftfc_1m  > 0.6
    ftfc_b5= _valid(ftfc_5m) and ftfc_5m  > 0.6
    st_b1  = _valid(st_1m)   and price    > st_1m
    st_b5  = _valid(st_5m)   and price_5m > st_5m
    vwap_b = _valid(vwap_val) and price   > vwap_val

    bull = {
        "sma20":       bs("SMA20 MTF",      2, sma_b1 and sma_b5,   f"{sma20_1m:.2f}" if _valid(sma20_1m) else "--", sma_b1, sma_b5),
        "adx":         bs("ADX Bull",        1, adx_b,               f"{adx_val:.1f}"  if _valid(adx_val)  else "--"),
        "rsi":         bs("RSI 45-65",       1, rsi_b,               f"{rsi_1m:.1f}"   if _valid(rsi_1m)   else "--"),
        "ftfc":        bs("FTFC MTF",        2, ftfc_b1 and ftfc_b5, f"{ftfc_1m*100:.0f}%" if _valid(ftfc_1m) else "--", ftfc_b1, ftfc_b5),
        "supertrend":  bs("SuperTrend MTF",  1, st_b1 and st_b5,    f"{st_1m:.2f}"    if _valid(st_1m)    else "--", st_b1, st_b5),
        "heikin_ashi": bs("HA Bull MTF",     1, ha_bull_1m and ha_bull_5m, "Bull" if ha_bull_1m else "Bear", ha_bull_1m, ha_bull_5m),
        "vwap":        bs("Above VWAP",      1, vwap_b,              f"{vwap_val:.2f}" if _valid(vwap_val) else "--"),
        "fvg":         bs("FVG Bull",        1, fvg_dir == 'bull',   fvg_dir.capitalize() if fvg_dir else "None"),
        "ob":          bs("Order Block Bull",1, ob_dir  == 'bull',   ob_dir.capitalize()  if ob_dir  else "None"),
        "rsi_div":     bs("RSI Div Bull",    1, rsi_div == 'bull',   rsi_div.capitalize() if rsi_div else "None"),
    }
    bull_score = sum(s['points'] for s in bull.values() if s['active'])

    # ---- Bear signals ----
    sma_r1  = _valid(sma20_1m) and price    < sma20_1m
    sma_r5  = _valid(sma20_5m) and price_5m < sma20_5m
    adx_r   = _valid(adx_val)  and adx_val > 22 and _valid(dmp_val) and _valid(dmn_val) and dmn_val > dmp_val
    rsi_r   = _valid(rsi_1m)   and 35 < rsi_1m < 55
    ftfc_r1 = _valid(ftfc_1m)  and ftfc_1m  < 0.4
    ftfc_r5 = _valid(ftfc_5m)  and ftfc_5m  < 0.4
    st_r1   = _valid(st_1m)    and price    < st_1m
    st_r5   = _valid(st_5m)    and price_5m < st_5m
    vwap_r  = _valid(vwap_val) and price    < vwap_val

    bear = {
        "sma20":       bs("SMA20 MTF",      2, sma_r1 and sma_r5,    f"{sma20_1m:.2f}" if _valid(sma20_1m) else "--", sma_r1, sma_r5),
        "adx":         bs("ADX Bear",        1, adx_r,                f"{adx_val:.1f}"  if _valid(adx_val)  else "--"),
        "rsi":         bs("RSI 35-55",       1, rsi_r,                f"{rsi_1m:.1f}"   if _valid(rsi_1m)   else "--"),
        "ftfc":        bs("FTFC Bear MTF",   2, ftfc_r1 and ftfc_r5,  f"{(1-ftfc_1m)*100:.0f}%" if _valid(ftfc_1m) else "--", ftfc_r1, ftfc_r5),
        "supertrend":  bs("SuperTrend MTF",  1, st_r1 and st_r5,     f"{st_1m:.2f}"    if _valid(st_1m)    else "--", st_r1, st_r5),
        "heikin_ashi": bs("HA Bear MTF",     1, (not ha_bull_1m) and (not ha_bull_5m), "Bear" if not ha_bull_1m else "Bull", not ha_bull_1m, not ha_bull_5m),
        "vwap":        bs("Below VWAP",      1, vwap_r,               f"{vwap_val:.2f}" if _valid(vwap_val) else "--"),
        "fvg":         bs("FVG Bear",        1, fvg_dir == 'bear',    fvg_dir.capitalize() if fvg_dir else "None"),
        "ob":          bs("OB Bear",         1, ob_dir  == 'bear',    ob_dir.capitalize()  if ob_dir  else "None"),
        "rsi_div":     bs("RSI Div Bear",    1, rsi_div == 'bear',    rsi_div.capitalize() if rsi_div else "None"),
    }
    bear_score = sum(s['points'] for s in bear.values() if s['active'])

    if bull_score > bear_score:
        direction = "BULL"
    elif bear_score > bull_score:
        direction = "BEAR"
    else:
        direction = "NEUTRAL"

    return {
        "price":       round(float(price), 2),
        "bull_score":  int(bull_score),
        "bear_score":  int(bear_score),
        "direction":   direction,
        "bull_signals": bull,
        "bear_signals": bear,
        "volume_spike": vol_spike,
        "vol_ratio":    vol_ratio,
    }


async def scan_ticker(client, ticker, market_open):
    print(f"Scanning {ticker}...", flush=True)

    df_1m = fetch_aggs(client, ticker, multiplier=1, days=5, limit=500)

    if df_1m is None or len(df_1m) < 50:
        print(f"⚠️ {ticker}: insufficient 1m data", flush=True)
        return

    df_5m = resample_to_5m(df_1m)   # resampled from 1m data, no extra API call
    if len(df_5m) < 20:
        df_5m = df_1m

    result = compute_signals(df_1m, df_5m)

    price      = result['price']
    bull_score = result['bull_score']
    bear_score = result['bear_score']
    direction  = result['direction']
    vol_spike  = result['volume_spike']
    score      = bull_score if direction != "BEAR" else bear_score

    if not market_open:
        status = "MARKET_CLOSED"
    elif score >= 8:
        status = "NORMAL"
    else:
        status = "REDUCED_RISK"

    # Append history once per minute
    history = dashboard_data[ticker]["history"]
    current_minute = datetime.now().strftime("%H:%M")
    if not history or history[-1]["time"] != current_minute:
        history.append({
            "time":       current_minute,
            "bull_score": int(bull_score),
            "bear_score": int(bear_score),
        })
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
        "bull_signals": result['bull_signals'],
        "bear_signals": result['bear_signals'],
        "history":      history,
    })

    # Log setup
    if score >= LOG_SCORE_THRESHOLD:
        global signal_log
        signal_log.insert(0, {
            "time":       datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "ticker":     ticker,
            "price":      price,
            "bull_score": bull_score,
            "bear_score": bear_score,
            "direction":  direction,
            "vol_spike":  vol_spike,
        })
        signal_log = signal_log[:200]
        save_signal_log(signal_log)

    # Send external notifications
    if market_open and score >= ALERT_SCORE_THRESHOLD:
        send_notifications(ticker, price, bull_score, bear_score, direction, vol_spike)

    # Volume spike notification (independent of score threshold)
    if market_open and vol_spike:
        ratio = result['vol_ratio'] or "?"
        print(f"⚡ VOLUME SPIKE [{ticker}]: {ratio}x avg", flush=True)

    print(
        f"[{datetime.now().strftime('%H:%M:%S')}] {ticker} ${price:.2f} | "
        f"Bull:{bull_score} Bear:{bear_score} | {direction} | {status}"
        + (" ⚡VOL" if vol_spike else ""),
        flush=True
    )


async def main():
    print("SCANNER STARTED", flush=True)
    if not POLYGON_API_KEY:
        print("ERROR: POLYGON_API_KEY not set", flush=True)
        return

    client = RESTClient(POLYGON_API_KEY)
    print(f"Scanning: {', '.join(WATCHLIST)}", flush=True)

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
  /* Ticker summary cards */
  .tcrd{background:#0d0d0d;border:1px solid #222;border-radius:10px;padding:14px 18px;cursor:pointer;transition:border-color .2s}
  .tcrd.active{border-color:#00ffcc}
  .tcrd:hover{border-color:#00ffcc88}
  .tcrd .t-ticker{font-size:1.1rem;font-weight:700;color:#fff}
  .tcrd .t-price{font-size:1.5rem;font-weight:700;color:#00ffcc;margin:4px 0}
  .tcrd .t-score{font-size:.82rem}
  .tcrd .t-dir{font-size:.8rem;font-weight:bold;padding:2px 8px;border-radius:10px}
  .dir-bull{background:#00ff8822;color:#00ff88;border:1px solid #00ff8855}
  .dir-bear{background:#ff444422;color:#ff6666;border:1px solid #ff444455}
  .dir-neutral{background:#44444422;color:#888;border:1px solid #555}
  .dir-starting{background:#ffaa0022;color:#ffaa00;border:1px solid #ffaa0055}
  /* Signal cards */
  .sig-card{background:#0c0c0c;border:1px solid #1a1a1a;border-radius:6px;padding:8px 10px;margin-bottom:6px;transition:border-color .25s}
  .sig-card.active{border-color:#00ff8866}
  .sig-card.inactive{opacity:.55}
  .sig-label{font-size:.65rem;color:#666;text-transform:uppercase;letter-spacing:.8px}
  .sig-val{font-size:.88rem;font-weight:600;margin-top:2px}
  .sig-icon{float:right;font-size:.9rem}
  .tf-badge{font-size:.58rem;padding:1px 5px;border-radius:8px;margin-left:3px}
  .tf-ok{background:#00ff8822;color:#00ff88}
  .tf-no{background:#ff444422;color:#ff6666}
  /* Score bars */
  .bar-wrap{background:#1a1a1a;border-radius:10px;height:7px;margin:4px 0}
  .bar{height:7px;border-radius:10px;transition:width .4s,background .4s}
  /* Tabs */
  .tab-btn{background:#111;border:1px solid #333;color:#888;padding:5px 14px;border-radius:6px;cursor:pointer;font-size:.82rem;transition:all .2s}
  .tab-btn.active{background:#00ffcc22;border-color:#00ffcc;color:#00ffcc}
  /* Alert items */
  .alert-item{background:#0d0d0d;border-left:3px solid #ff9900;padding:7px 10px;margin-bottom:5px;border-radius:0 5px 5px 0;font-size:.78rem}
  /* Status badge */
  .sb{font-size:.78rem;padding:3px 10px;border-radius:12px;font-weight:600}
  .sb-normal{background:#00ff8822;color:#00ff88;border:1px solid #00ff88}
  .sb-risk{background:#ff444422;color:#ff4444;border:1px solid #ff4444}
  .sb-closed{background:#22222288;color:#666;border:1px solid #444}
  .sb-starting{background:#ffaa0022;color:#ffaa00;border:1px solid #ffaa00}
  /* Signal log table */
  .log-table{width:100%;font-size:.78rem;border-collapse:collapse}
  .log-table th{color:#555;text-transform:uppercase;font-size:.65rem;letter-spacing:.8px;padding:4px 8px;border-bottom:1px solid #1e1e1e}
  .log-table td{padding:5px 8px;border-bottom:1px solid #111}
  .log-bull{color:#00ff88}.log-bear{color:#ff6666}.log-neutral{color:#888}
  /* Misc */
  .section-title{color:#555;font-size:.65rem;text-transform:uppercase;letter-spacing:1.5px;margin-bottom:8px}
  .live-dot{display:inline-block;width:7px;height:7px;background:#00ff88;border-radius:50%;margin-right:6px;animation:pulse 2s infinite}
  .live-dot.off{background:#444;animation:none}
  @keyframes pulse{0%,100%{opacity:1}50%{opacity:.25}}
  .vol-spike{background:#ff990022;border:1px solid #ff9900;color:#ff9900;border-radius:5px;padding:2px 8px;font-size:.72rem}
  .sound-btn{background:#111;border:1px solid #333;color:#888;padding:4px 12px;border-radius:6px;cursor:pointer;font-size:.78rem}
  .sound-btn.on{border-color:#00ffcc;color:#00ffcc}
</style>
</head>
<body class="p-3">
<div class="container-fluid">

  <!-- Header -->
  <div class="d-flex align-items-center gap-3 mb-3 flex-wrap">
    <span class="live-dot" id="live-dot"></span>
    <h1>SPX Confluence Scanner</h1>
    <span id="mkt-badge" class="sb sb-starting">STARTING</span>
    <span class="ms-auto text-muted" style="font-size:.75rem">Updated: <span id="last-update">--</span></span>
    <button class="sound-btn on" id="sound-btn" onclick="toggleSound()">🔔 Sound ON</button>
  </div>

  <!-- Ticker Summary Row -->
  <div class="row g-2 mb-3" id="ticker-row"></div>

  <!-- Detail Panel -->
  <div class="card p-3 mb-3">
    <div class="d-flex align-items-center gap-2 mb-3" id="detail-header">
      <div class="section-title mb-0" id="detail-title">SPY — Signals</div>
      <div class="ms-2 d-flex gap-1" id="dir-tabs">
        <button class="tab-btn active" id="tab-bull" onclick="setDir('bull')">🔼 Bull</button>
        <button class="tab-btn"        id="tab-bear" onclick="setDir('bear')">🔽 Bear</button>
      </div>
      <span id="vol-spike-badge" class="vol-spike d-none ms-2">⚡ VOL SPIKE</span>
    </div>
    <div class="row g-2" id="signal-grid"></div>
  </div>

  <!-- Charts Row -->
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
        <div id="alerts-panel"><span class="text-muted">No alerts yet</span></div>
      </div>
    </div>
    <div class="col-md-3">
      <div class="card p-3 h-100">
        <div class="section-title">TradingView</div>
        <iframe src="https://www.tradingview.com/widgetembed/?symbol=AMEX:SPY&interval=1&theme=dark"
          width="100%" height="220" frameborder="0" id="tv-frame"></iframe>
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
          <th>Bull</th><th>Bear</th><th>Direction</th><th>Vol</th>
        </tr></thead>
        <tbody id="log-body"><tr><td colspan="7" style="color:#555;text-align:center">No setups logged yet</td></tr></tbody>
      </table>
    </div>
  </div>

</div><!-- /container -->

<script>
// ---- State ----
let allData   = {};
let signalLog = [];
let curTicker = 'SPY';
let curDir    = 'bull';
let soundOn   = true;
let prevScores = {};   // {ticker: {bull, bear}}
let scoreChart = null;

const MAX_SCORE = """ + str(MAX_SCORE) + """;

// ---- Sound ----
function toggleSound() {
  soundOn = !soundOn;
  const btn = document.getElementById('sound-btn');
  btn.textContent = soundOn ? '🔔 Sound ON' : '🔕 Sound OFF';
  btn.className = soundOn ? 'sound-btn on' : 'sound-btn';
}

function playAlert(freq, count) {
  const ACtx = window.AudioContext || window.webkitAudioContext;
  if (!ACtx || !soundOn) return;
  const ctx = new ACtx();
  for (let i = 0; i < (count || 1); i++) {
    const osc  = ctx.createOscillator();
    const gain = ctx.createGain();
    osc.connect(gain); gain.connect(ctx.destination);
    osc.frequency.value = freq || 880;
    osc.type = 'sine';
    const t = ctx.currentTime + i * 0.18;
    gain.gain.setValueAtTime(0.25, t);
    gain.gain.exponentialRampToValueAtTime(0.001, t + 0.25);
    osc.start(t); osc.stop(t + 0.25);
  }
}

// ---- Score color ----
function scoreColor(s) {
  const p = s / MAX_SCORE;
  if (p >= 0.75) return '#00ff88';
  if (p >= 0.55) return '#aaff00';
  if (p >= 0.35) return '#ffaa00';
  return '#ff4444';
}

// ---- Ticker cards ----
function renderTickerRow() {
  const row = document.getElementById('ticker-row');
  row.innerHTML = '';
  for (const ticker of Object.keys(allData)) {
    const d = allData[ticker];
    const score  = d.direction === 'BEAR' ? d.bear_score : d.bull_score;
    const dirCls = {BULL:'dir-bull',BEAR:'dir-bear',NEUTRAL:'dir-neutral',STARTING:'dir-starting'}[d.direction] || 'dir-starting';
    const col = document.createElement('div');
    col.className = 'col';
    col.innerHTML = `
      <div class="tcrd${ticker===curTicker?' active':''}" onclick="selectTicker('${ticker}')">
        <div class="d-flex justify-content-between align-items-start">
          <span class="t-ticker">${ticker}</span>
          <span class="t-dir ${dirCls}">${d.direction}</span>
        </div>
        <div class="t-price">$${d.price.toFixed(2)}</div>
        <div class="t-score d-flex gap-2">
          <span style="color:#00ff88">▲${d.bull_score}</span>
          <span style="color:#ff6666">▼${d.bear_score}</span>
          <span style="color:#555">/${MAX_SCORE}</span>
          ${d.volume_spike ? '<span class="vol-spike">⚡</span>' : ''}
        </div>
        <div class="bar-wrap mt-1">
          <div class="bar" style="width:${Math.min(score/MAX_SCORE*100,100)}%;background:${scoreColor(score)}"></div>
        </div>
      </div>`;
    row.appendChild(col);
  }
}

// ---- Select ticker ----
function selectTicker(ticker) {
  curTicker = ticker;
  renderTickerRow();
  renderSignals();
  renderAlerts();
  updateChart();
  document.getElementById('detail-title').textContent = ticker + ' — Signals';
  document.getElementById('chart-ticker').textContent = ticker;
  const tvSym = {SPY:'AMEX:SPY',QQQ:'NASDAQ:QQQ',IWM:'AMEX:IWM'}[ticker] || 'AMEX:SPY';
  document.getElementById('tv-frame').src =
    `https://www.tradingview.com/widgetembed/?symbol=${tvSym}&interval=1&theme=dark`;
}

// ---- Dir tabs ----
function setDir(dir) {
  curDir = dir;
  document.getElementById('tab-bull').className = 'tab-btn' + (dir==='bull'?' active':'');
  document.getElementById('tab-bear').className = 'tab-btn' + (dir==='bear'?' active':'');
  renderSignals();
}

// ---- Signal grid ----
function renderSignals() {
  const d = allData[curTicker];
  if (!d) return;
  const signals = curDir === 'bull' ? d.bull_signals : d.bear_signals;
  const grid = document.getElementById('signal-grid');
  grid.innerHTML = '';
  for (const [, sig] of Object.entries(signals)) {
    const col = document.createElement('div');
    col.className = 'col-6 col-xl-4 col-xxl-3';
    let tfHtml = '';
    if (sig.tf1 !== undefined) {
      tfHtml = `<span class="tf-badge ${sig.tf1?'tf-ok':'tf-no'}">1m</span>`
             + `<span class="tf-badge ${sig.tf5?'tf-ok':'tf-no'}">5m</span>`;
    }
    const color = sig.active ? (curDir==='bull'?'#00ff88':'#ff6666') : '#444';
    col.innerHTML = `<div class="sig-card ${sig.active?'active':'inactive'}">
      <span class="sig-icon">${sig.active?(curDir==='bull'?'✅':'🔴'):'❌'}</span>
      <div class="sig-label">${sig.label} ${tfHtml} <small style="color:#555">${sig.points}pt</small></div>
      <div class="sig-val" style="color:${color}">${sig.value}</div>
    </div>`;
    grid.appendChild(col);
  }
  const d2 = allData[curTicker];
  const vsBadge = document.getElementById('vol-spike-badge');
  if (d2 && d2.volume_spike) {
    vsBadge.classList.remove('d-none');
    vsBadge.textContent = '⚡ VOL SPIKE ' + (d2.vol_ratio ? d2.vol_ratio + 'x' : '');
  } else {
    vsBadge.classList.add('d-none');
  }
}

// ---- Alerts ----
function renderAlerts() {
  const d = allData[curTicker];
  if (!d) return;
  const panel = document.getElementById('alerts-panel');
  if (!d.alerts || d.alerts.length === 0) {
    panel.innerHTML = '<span class="text-muted" style="font-size:.82rem">No alerts yet</span>';
    return;
  }
  panel.innerHTML = d.alerts.map(a => {
    const clr = a.direction==='BULL'?'#00ff88':'#ff6666';
    return `<div class="alert-item">
      <span style="color:#ffaa00">${a.time}</span>
      <span class="ms-2" style="color:${clr};font-weight:600">${a.direction}</span>
      <span class="ms-2">$${a.price.toFixed(2)}</span>
      <span class="ms-2 text-muted">Score ${a.score}</span>
      <div style="color:#888;font-size:.72rem;margin-top:2px">${a.message}</div>
    </div>`;
  }).join('');
}

// ---- Chart ----
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
      responsive:true,
      animation:{duration:250},
      interaction:{mode:'index',intersect:false},
      scales:{
        x:{ticks:{color:'#444',maxTicksLimit:8,font:{size:9}},grid:{color:'#1a1a1a'}},
        y:{min:0,max:MAX_SCORE,ticks:{color:'#444',stepSize:2},grid:{color:'#1a1a1a'}}
      },
      plugins:{legend:{labels:{color:'#555',font:{size:10}}}}
    }
  });
}

function updateChart() {
  const d = allData[curTicker];
  if (!d || !d.history || d.history.length === 0 || !scoreChart) return;
  scoreChart.data.labels = d.history.map(h => h.time);
  scoreChart.data.datasets[0].data = d.history.map(h => h.bull_score);
  scoreChart.data.datasets[1].data = d.history.map(h => h.bear_score);
  scoreChart.update('none');
}

// ---- Signal log ----
function renderLog() {
  const tbody = document.getElementById('log-body');
  if (!signalLog || signalLog.length === 0) return;
  tbody.innerHTML = signalLog.slice(0, 50).map(e => {
    const dirCls = e.direction==='BULL'?'log-bull':e.direction==='BEAR'?'log-bear':'log-neutral';
    return `<tr>
      <td style="color:#555">${e.time}</td>
      <td style="font-weight:600">${e.ticker}</td>
      <td>$${e.price.toFixed(2)}</td>
      <td class="log-bull">${e.bull_score}</td>
      <td class="log-bear">${e.bear_score}</td>
      <td class="${dirCls} fw-bold">${e.direction}</td>
      <td>${e.vol_spike ? '⚡' : ''}</td>
    </tr>`;
  }).join('');
}

// ---- Main update loop ----
async function update() {
  try {
    const res  = await fetch('/api/status');
    const data = await res.json();
    allData   = data.tickers || {};
    signalLog = data.signal_log || [];

    // Market badge
    const mktBadge = document.getElementById('mkt-badge');
    if (data.market_open) {
      mktBadge.className = 'sb sb-normal'; mktBadge.textContent = 'MARKET OPEN';
      document.getElementById('live-dot').className = 'live-dot';
    } else {
      mktBadge.className = 'sb sb-closed'; mktBadge.textContent = 'MARKET CLOSED';
      document.getElementById('live-dot').className = 'live-dot off';
    }

    // Sound check & last-update
    let latestUpdate = '--';
    for (const [ticker, d] of Object.entries(allData)) {
      const prev = prevScores[ticker] || {bull:0,bear:0};
      const newBull = d.bull_score, newBear = d.bear_score;
      const prevMax = Math.max(prev.bull, prev.bear);
      const newMax  = Math.max(newBull, newBear);
      if (newMax >= 8 && newMax > prevMax) {
        playAlert(newMax >= 10 ? 1100 : 880, newMax >= 10 ? 3 : 2);
      }
      prevScores[ticker] = {bull: newBull, bear: newBear};
      if (d.last_update !== 'N/A') latestUpdate = d.last_update;
    }
    document.getElementById('last-update').textContent = latestUpdate;

    renderTickerRow();
    renderSignals();
    renderAlerts();
    updateChart();
    renderLog();
  } catch(e) {
    console.error('Update error:', e);
  }
}

// ---- Init ----
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
