import asyncio
import csv
import itertools
import json
import math
import os
import smtplib
import threading
import time
import traceback
from datetime import datetime, date, timedelta, timezone
from email.mime.text import MIMEText

import pandas as pd
import pandas_ta as ta
import requests
import yfinance as yf
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
MAX_SCORE             = 18       # 17 Phase-2 + Put/Call Ratio (1pt per direction)
ALERT_COOLDOWN_SECS   = 900
VOLUME_SPIKE_MULT     = 3.0
ALERT_SCORE_THRESHOLD = 9
LOG_SCORE_THRESHOLD   = 6
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


# ====================== TRADE TRACKING (Phase 6) ======================

def track_signal(ticker, price, stop, tp, direction, score):
    """Open a simulated trade. One open trade per ticker+direction at a time."""
    for t in open_trades.values():
        if t["ticker"] == ticker and t["direction"] == direction:
            return  # already tracking this setup
    trade_id = f"{ticker}_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
    open_trades[trade_id] = {
        "id":        trade_id,
        "ticker":    ticker,
        "direction": direction,
        "entry":     round(float(price), 4),
        "stop":      round(float(stop),  4),
        "tp":        round(float(tp),    4),
        "score":     score,
        "open_time": datetime.now().isoformat(),
        "open_ts":   time.time(),
    }
    print(f"[TRADE] OPEN {ticker} {direction} @ ${price:.2f} SL${stop:.2f} TP${tp:.2f} [{score}/{MAX_SCORE}]", flush=True)


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
    if stop and tp:
        track_signal(ticker, price, stop, tp, direction, score)

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
    "pcr":          None,
    "pcr_oi":       None,
    "call_vol":     None,
    "put_vol":      None,
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


def compute_signals(df_1m, df_5m, ticker=None):
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

    # ── Put/Call Ratio signal (uses global options_data, fetched via yfinance) ─
    opts      = options_data.get(ticker, {}) if ticker else {}
    pcr       = opts.get("pcr")
    pcr_bull  = bool(_valid(pcr) and float(pcr) < PCR_BULL_THRESH)   # calls dominating
    pcr_bear  = bool(_valid(pcr) and float(pcr) > PCR_BEAR_THRESH)   # puts dominating
    pcr_label = f"{pcr:.2f}" if _valid(pcr) else "No data"

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
        "pcr":         bs("P/C Ratio Bull",   1, pcr_bull,               pcr_label),
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
        "pcr":         bs("P/C Ratio Bear",   1, pcr_bear,               pcr_label),
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
        options_data[ticker_sym] = {
            "pcr":         pcr_vol,
            "pcr_oi":      pcr_oi,
            "call_vol":    int(call_vol),
            "put_vol":     int(put_vol),
            "expiry":      exps[0],
            "last_update": datetime.now().strftime("%H:%M:%S"),
        }
        # Update dashboard_data so it's visible immediately
        if ticker_sym in dashboard_data:
            dashboard_data[ticker_sym].update({
                "pcr":      pcr_vol,
                "pcr_oi":   pcr_oi,
                "call_vol": int(call_vol),
                "put_vol":  int(put_vol),
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

    result    = compute_signals(df_1m, df_5m, ticker=ticker)
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
        # PCR from options_data (updated by fetch_options_flow, not per-scan)
        "pcr":          options_data.get(ticker, {}).get("pcr"),
        "pcr_oi":       options_data.get(ticker, {}).get("pcr_oi"),
        "call_vol":     options_data.get(ticker, {}).get("call_vol"),
        "put_vol":      options_data.get(ticker, {}).get("put_vol"),
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

    client          = RESTClient(POLYGON_API_KEY)
    loop            = asyncio.get_event_loop()
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
            et_now = datetime.now(timezone.utc).astimezone(
                __import__('zoneinfo', fromlist=['ZoneInfo']).ZoneInfo('America/New_York')
            )
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
          <th>Bull</th><th>Bear</th><th>Dir</th>
          <th>ATR</th><th>Stop</th><th>TP</th><th>Gap</th><th>Vol</th>
        </tr></thead>
        <tbody id="log-body">
          <tr><td colspan="11" style="color:#555;text-align:center;padding:12px">No setups logged yet</td></tr>
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
let curTicker    = 'SPY';
let curDir       = 'bull';
let soundOn      = true;
let prevScores   = {};
let scoreChart   = null;

const MAX_SCORE           = """ + str(MAX_SCORE) + """;
const ALERT_SCORE_THRESH  = """ + str(ALERT_SCORE_THRESHOLD) + """;
const LOG_SCORE_THRESH    = """ + str(LOG_SCORE_THRESHOLD) + """;

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

function fireNotification(ticker, direction, score) {
  if (!notifGranted) return;
  const emoji = direction === 'BULL' ? '🚀' : '🔻';
  try {
    new Notification(`${emoji} ${ticker} ${direction} — ${score}/${MAX_SCORE}`, {
      body: `Confluence score ${score}/${MAX_SCORE} — check the scanner`,
      tag: ticker,
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

  // PCR chip
  const d2 = allData[curTicker];
  if (d2 && d2.pcr != null) {
    const pcrCls = d2.pcr < """ + str(0.7) + """ ? 'ctx-bull' : d2.pcr > """ + str(1.2) + """ ? 'ctx-bear' : 'ctx-neutral';
    html += `<span class="ctx-badge ${pcrCls}" title="Put/Call ratio (volume) — nearest expiry">P/C ${d2.pcr.toFixed(2)} ${d2.pcr<0.7?'↑calls':d2.pcr>1.2?'↑puts':'~'}</span>`;
    if (d2.call_vol && d2.put_vol)
      html += `<span class="ctx-badge ctx-neutral" title="Options volume">C:${(d2.call_vol/1000).toFixed(0)}k P:${(d2.put_vol/1000).toFixed(0)}k</span>`;
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
  </div>`}
  ${opens.length > 0 ? `
  <div class="section-title mt-2">Open Positions (${opens.length})</div>
  ${opens.map(t => {
    const dc = t.direction==='BULL'?'#00ff88':'#ff6666';
    const elapsed = Math.round((Date.now()/1000 - t.open_ts)/60);
    return `<div style="font-size:.74rem;padding:3px 0;border-bottom:1px solid #0d0d0d">
      <span style="color:${dc};font-weight:600">${t.direction}</span>
      <span class="ms-1 fw-bold">${t.ticker}</span>
      <span class="ms-1" style="color:#777">entry $${t.entry.toFixed(2)}</span>
      <span class="ms-1" style="color:#ff6666">SL $${t.stop.toFixed(2)}</span>
      <span class="ms-1" style="color:#00ff88">TP $${t.tp.toFixed(2)}</span>
      <span class="ms-2" style="color:#555">[${t.score}/${MAX_SCORE}]</span>
      <span class="ms-2" style="color:#444">${elapsed}m ago</span>
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

  const scoreDist = {};
  for (let i = LOG_SCORE_THRESH; i <= MAX_SCORE; i++) scoreDist[i] = 0;
  for (const e of src) {
    const s = Math.max(e.bull_score || 0, e.bear_score || 0);
    if (s >= LOG_SCORE_THRESH) scoreDist[s] = (scoreDist[s] || 0) + 1;
  }
  const maxScoreCnt = Math.max(...Object.values(scoreDist), 1);

  const top5 = [...src].sort((a,b) =>
    Math.max(b.bull_score||0,b.bear_score||0) - Math.max(a.bull_score||0,a.bear_score||0)
  ).slice(0, 5);

  panel.innerHTML = tradesHtml + `
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
      const color = si >= 13 ? '#00ff88' : si >= 10 ? '#aaff00' : si >= ALERT_SCORE_THRESH ? '#ffaa00' : '#ff6666';
      return `<div class="d-flex align-items-center gap-2 mb-1" style="font-size:.76rem">
        <span style="width:18px;color:#555;text-align:right">${s}</span>
        ${miniBar(n/maxScoreCnt*100, color)}
        <span style="width:18px;color:#555;text-align:right">${n}</span>
      </div>`;
    }).join('')}
  </div>
  <div class="col-12 col-md-3">
    <div class="section-title">Top Setups</div>
    ${top5.map(e => {
      const score = Math.max(e.bull_score||0, e.bear_score||0);
      const dc    = e.direction==='BULL'?'#00ff88':'#ff6666';
      const vol   = e.vol_spike ? ' ⚡' : '';
      const gap   = e.gap_pct != null ? ` ${e.gap_pct>0?'+':''}${parseFloat(e.gap_pct).toFixed(1)}%` : '';
      const ts    = (e.time||'').slice(11,16);
      return `<div style="padding:4px 0;border-bottom:1px solid #111;font-size:.73rem">
        <span style="color:#555">${ts}</span>
        <span class="ms-1 fw-bold">${e.ticker}</span>
        <span class="ms-1" style="color:#777">$${parseFloat(e.price||0).toFixed(0)}</span>
        <span class="ms-1 fw-bold" style="color:${dc}">${e.direction}</span>
        <span class="ms-1" style="color:#aaa">${score}/${MAX_SCORE}${vol}${gap}</span>
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
    const [res, resT] = await Promise.all([
      fetch('/api/status'),
      fetch('/api/outcomes'),
    ]);
    const data = await res.json();
    const tdata = resT.ok ? await resT.json() : {open_trades:[], outcomes:[]};
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
      if (newMax >= 8 && newMax > prevMax) {
        playAlert(newMax >= 11 ? 1100 : 880, newMax >= 11 ? 3 : 2);
        if (newMax >= ALERT_SCORE_THRESH) fireNotification(ticker, d.direction, newMax);
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

# ====================== START ======================
threading.Thread(
    target=lambda: asyncio.run(main()),
    daemon=True
).start()

if __name__ == "__main__":
    app.run(host='0.0.0.0', port=8080, debug=False)
