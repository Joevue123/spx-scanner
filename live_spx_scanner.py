import asyncio
import itertools
import json
import math
import os
import threading
import traceback
from datetime import datetime, timedelta, timezone

import pandas as pd
import pandas_ta as ta
import requests
from flask import Flask, jsonify
from polygon import RESTClient

# ====================== CONFIG ======================
POLYGON_API_KEY = os.getenv("POLYGON_API_KEY")
DISCORD_WEBHOOK = os.getenv("DISCORD_WEBHOOK")
HISTORY_FILE = "/tmp/score_history.json"
MAX_SCORE = 11

print("=== FULL SPX CONFLUENCE SCANNER STARTING ===", flush=True)

# ====================== HELPERS ======================

def _valid(v):
    try:
        return v is not None and not math.isnan(float(v))
    except (TypeError, ValueError):
        return False


def is_market_open():
    now = datetime.now(timezone.utc)
    if now.weekday() >= 5:
        return False
    # NYSE: 9:30-16:00 ET. EDT=UTC-4 (Mar-Nov), EST=UTC-5 (Nov-Mar)
    utc_offset = 4 if 3 <= now.month <= 11 else 5
    market_open  = now.replace(hour=9  + utc_offset, minute=30, second=0, microsecond=0)
    market_close = now.replace(hour=16 + utc_offset, minute=0,  second=0, microsecond=0)
    return market_open <= now <= market_close


def load_history():
    try:
        with open(HISTORY_FILE) as f:
            return json.load(f)
    except Exception:
        return []


def save_history(history):
    try:
        with open(HISTORY_FILE, "w") as f:
            json.dump(history, f)
    except Exception:
        pass


# ====================== STATE ======================
app = Flask(__name__)

dashboard_data = {
    "price":       0.0,
    "score":       0,
    "max_score":   MAX_SCORE,
    "status":      "STARTING",
    "last_update": "N/A",
    "market_open": False,
    "signals": {
        "sma20":       {"value": "--", "active": False, "label": "Above SMA20",  "points": 2},
        "adx":         {"value": "--", "active": False, "label": "ADX > 22",     "points": 1},
        "rsi":         {"value": "--", "active": False, "label": "RSI 45-65",    "points": 1},
        "ftfc":        {"value": "--", "active": False, "label": "FTFC > 60%",   "points": 2},
        "supertrend":  {"value": "--", "active": False, "label": "SuperTrend",   "points": 1},
        "heikin_ashi": {"value": "--", "active": False, "label": "Heikin Ashi",  "points": 1},
        "vwap":        {"value": "--", "active": False, "label": "Above VWAP",   "points": 1},
        "fvg":         {"value": "--", "active": False, "label": "FVG Active",   "points": 1},
        "ob":          {"value": "--", "active": False, "label": "Order Block",  "points": 1},
    },
    "history": load_history(),
    "alerts":  [],
}

# ====================== DISCORD ======================

def send_discord_alert(price, score, message="Strong Signal"):
    if not DISCORD_WEBHOOK:
        print("Discord webhook not configured", flush=True)
        return
    try:
        payload = {
            "content": (
                f"🚨 **SPY Scanner Alert** 🚨\n"
                f"**Price:** {price:.2f}\n"
                f"**Score:** {score}/{MAX_SCORE}\n"
                f"**Signal:** {message}\n"
                f"**Time:** {datetime.now().strftime('%H:%M:%S')}"
            )
        }
        requests.post(DISCORD_WEBHOOK, json=payload, timeout=5)
        dashboard_data["alerts"].insert(0, {
            "time":    datetime.now().strftime("%H:%M:%S"),
            "price":   round(float(price), 2),
            "score":   score,
            "message": message,
        })
        dashboard_data["alerts"] = dashboard_data["alerts"][:10]
        print("✅ Discord alert sent", flush=True)
    except Exception as e:
        print(f"Discord failed: {e}", flush=True)

# ====================== DASHBOARD HTML ======================

DASHBOARD_HTML = """<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>SPY Confluence Scanner</title>
    <link href="https://cdn.jsdelivr.net/npm/bootstrap@5.3.3/dist/css/bootstrap.min.css" rel="stylesheet">
    <script src="https://cdn.jsdelivr.net/npm/chart.js"></script>
    <style>
        body { background: #0a0a0a; color: #e0e0e0; font-family: 'Segoe UI', sans-serif; }
        .card { background: #111; border: 1px solid #222; border-radius: 10px; }
        .price { font-size: 2.8rem; font-weight: bold; color: #00ffcc; }
        .score-value { font-size: 2.8rem; font-weight: bold; }
        .score-bar-wrap { background: #222; border-radius: 20px; height: 12px; margin-top: 8px; }
        .score-bar { height: 12px; border-radius: 20px; transition: width 0.5s ease, background 0.5s ease; }
        .signal-card { background: #0d0d0d; border: 1px solid #1a1a1a; border-radius: 8px; padding: 10px 12px; margin-bottom: 8px; transition: border-color 0.3s; }
        .signal-card.active { border-color: #00ff88; }
        .signal-card.inactive { border-color: #333; opacity: 0.6; }
        .signal-label { font-size: 0.7rem; color: #888; text-transform: uppercase; letter-spacing: 1px; }
        .signal-value { font-size: 0.95rem; font-weight: bold; margin-top: 2px; }
        .signal-icon { font-size: 1rem; float: right; }
        .alert-item { background: #0d0d0d; border-left: 3px solid #ff9900; padding: 8px 12px; margin-bottom: 6px; border-radius: 0 6px 6px 0; font-size: 0.82rem; }
        .status-badge { font-size: 0.95rem; padding: 5px 14px; border-radius: 20px; font-weight: bold; }
        .status-normal   { background: #00ff8822; color: #00ff88; border: 1px solid #00ff88; }
        .status-risk     { background: #ff444422; color: #ff4444; border: 1px solid #ff4444; }
        .status-closed   { background: #44444422; color: #888;    border: 1px solid #555; }
        .status-starting { background: #ffaa0022; color: #ffaa00; border: 1px solid #ffaa00; }
        .section-title { color: #666; font-size: 0.7rem; text-transform: uppercase; letter-spacing: 2px; margin-bottom: 10px; }
        .live-dot { display: inline-block; width: 8px; height: 8px; background: #00ff88; border-radius: 50%; margin-right: 8px; animation: pulse 2s infinite; }
        .live-dot.closed { background: #555; animation: none; }
        @keyframes pulse { 0%,100%{opacity:1} 50%{opacity:0.3} }
        h1 { color: #00ffcc; font-size: 1.5rem; margin: 0; }
        .chart-wrap { background: #111; border: 1px solid #222; border-radius: 10px; padding: 16px; }
        .market-closed-banner { background: #1a1a1a; border: 1px solid #444; border-radius: 8px; padding: 6px 14px; font-size: 0.8rem; color: #888; }
    </style>
</head>
<body class="p-3">
<div class="container-fluid">

    <div class="d-flex align-items-center mb-3 gap-3 flex-wrap">
        <span class="live-dot" id="live-dot"></span>
        <h1>SPY Confluence Scanner</h1>
        <span id="status-badge" class="status-badge status-starting ms-1">STARTING</span>
        <span id="market-banner" class="market-closed-banner d-none">Market Closed — showing last session data</span>
        <span class="ms-auto text-muted" style="font-size:0.8rem;">Updated: <span id="last_update">--</span></span>
    </div>

    <div class="row g-3 mb-3">
        <div class="col-md-4">
            <div class="card p-4 h-100">
                <div class="section-title">SPY Price</div>
                <div class="price" id="price">--</div>
            </div>
        </div>
        <div class="col-md-4">
            <div class="card p-4 h-100">
                <div class="section-title">Confluence Score</div>
                <div class="d-flex align-items-baseline gap-1">
                    <div class="score-value" id="score-val">--</div>
                    <div class="text-muted" id="score-max" style="font-size:1.1rem;">/11</div>
                </div>
                <div class="score-bar-wrap">
                    <div class="score-bar" id="score-bar" style="width:0%"></div>
                </div>
            </div>
        </div>
        <div class="col-md-4">
            <div class="card p-4 h-100">
                <div class="section-title">Governance Status</div>
                <div id="scanner-status" style="font-size:1.4rem; font-weight:bold; margin-top:4px;">--</div>
            </div>
        </div>
    </div>

    <div class="row g-3 mb-3">
        <div class="col-md-7">
            <div class="card p-3 h-100">
                <div class="section-title">Signal Breakdown</div>
                <div class="row g-2" id="signals-grid"></div>
            </div>
        </div>
        <div class="col-md-5">
            <div class="card p-3 h-100">
                <div class="section-title">Recent Alerts</div>
                <div id="alerts-panel">
                    <div class="text-muted" style="font-size:0.85rem;">No alerts yet</div>
                </div>
            </div>
        </div>
    </div>

    <div class="row g-3">
        <div class="col-md-5">
            <div class="chart-wrap h-100">
                <div class="section-title">Score History</div>
                <canvas id="scoreChart"></canvas>
            </div>
        </div>
        <div class="col-md-7">
            <div class="chart-wrap">
                <div class="section-title">SPY Live Chart</div>
                <iframe src="https://www.tradingview.com/widgetembed/?symbol=AMEX:SPY&interval=1&theme=dark"
                    width="100%" height="340" frameborder="0"></iframe>
            </div>
        </div>
    </div>

</div>
<script>
const ctx = document.getElementById('scoreChart').getContext('2d');
const scoreChart = new Chart(ctx, {
    type: 'line',
    data: {
        labels: [],
        datasets: [{
            label: 'Score',
            data: [],
            borderColor: '#00ffcc',
            backgroundColor: 'rgba(0,255,204,0.07)',
            tension: 0.3,
            pointRadius: 2,
            fill: true
        }]
    },
    options: {
        responsive: true,
        animation: { duration: 300 },
        scales: {
            x: { ticks: { color: '#555', maxTicksLimit: 8, font: {size:10} }, grid: { color: '#1a1a1a' } },
            y: { min: 0, max: 11, ticks: { color: '#555', stepSize: 1 }, grid: { color: '#1a1a1a' } }
        },
        plugins: { legend: { display: false } }
    }
});

function scoreColor(s, max) {
    const pct = s / max;
    if (pct >= 0.82) return '#00ff88';
    if (pct >= 0.64) return '#aaff00';
    if (pct >= 0.45) return '#ffaa00';
    return '#ff4444';
}

function updateSignals(signals) {
    const grid = document.getElementById('signals-grid');
    grid.innerHTML = '';
    for (const [, sig] of Object.entries(signals)) {
        const col = document.createElement('div');
        col.className = 'col-6 col-xl-4';
        col.innerHTML =
            '<div class="signal-card ' + (sig.active ? 'active' : 'inactive') + '">' +
            '<span class="signal-icon">' + (sig.active ? '✅' : '❌') + '</span>' +
            '<div class="signal-label">' + sig.label + (sig.points > 1 ? ' (' + sig.points + 'pt)' : '') + '</div>' +
            '<div class="signal-value" style="color:' + (sig.active ? '#00ff88' : '#666') + '">' + sig.value + '</div>' +
            '</div>';
        grid.appendChild(col);
    }
}

function updateAlerts(alerts) {
    const panel = document.getElementById('alerts-panel');
    if (!alerts || alerts.length === 0) {
        panel.innerHTML = '<div class="text-muted" style="font-size:0.85rem;">No alerts yet</div>';
        return;
    }
    panel.innerHTML = alerts.map(function(a) {
        return '<div class="alert-item">' +
            '<span class="text-warning">' + a.time + '</span>' +
            '<span class="ms-2 text-light">$' + a.price.toFixed(2) + '</span>' +
            '<span class="ms-2 text-success fw-bold">Score ' + a.score + '</span>' +
            '<div style="color:#aaa;font-size:0.78rem;margin-top:2px;">' + a.message + '</div>' +
            '</div>';
    }).join('');
}

async function updateDashboard() {
    try {
        const res = await fetch('/api/status');
        const data = await res.json();

        const maxScore = data.max_score || 11;
        document.getElementById('score-max').textContent = '/' + maxScore;

        document.getElementById('price').textContent = parseFloat(data.price).toFixed(2);

        const score = data.score;
        const color = scoreColor(score, maxScore);
        const scoreEl = document.getElementById('score-val');
        scoreEl.textContent = score;
        scoreEl.style.color = color;
        document.getElementById('score-bar').style.width = Math.min(score / maxScore * 100, 100) + '%';
        document.getElementById('score-bar').style.background = color;

        const badge = document.getElementById('status-badge');
        const statusEl = document.getElementById('scanner-status');
        const dot = document.getElementById('live-dot');
        const banner = document.getElementById('market-banner');

        badge.className = 'status-badge';
        if (data.status === 'NORMAL') {
            badge.classList.add('status-normal');
            statusEl.style.color = '#00ff88';
            dot.className = 'live-dot';
            banner.classList.add('d-none');
        } else if (data.status === 'REDUCED_RISK') {
            badge.classList.add('status-risk');
            statusEl.style.color = '#ff4444';
            dot.className = 'live-dot';
            banner.classList.add('d-none');
        } else if (data.status === 'MARKET_CLOSED') {
            badge.classList.add('status-closed');
            statusEl.style.color = '#888';
            dot.className = 'live-dot closed';
            banner.classList.remove('d-none');
        } else {
            badge.classList.add('status-starting');
            statusEl.style.color = '#ffaa00';
            dot.className = 'live-dot';
            banner.classList.add('d-none');
        }
        badge.textContent = data.status;
        statusEl.textContent = data.status;

        document.getElementById('last_update').textContent = data.last_update;

        if (data.signals) updateSignals(data.signals);
        if (data.alerts !== undefined) updateAlerts(data.alerts);

        if (data.history && data.history.length > 0) {
            scoreChart.data.labels = data.history.map(function(h){ return h.time; });
            scoreChart.data.datasets[0].data = data.history.map(function(h){ return h.score; });
            scoreChart.data.datasets[0].borderColor = color;
            scoreChart.options.scales.y.max = maxScore;
            scoreChart.update();
        }
    } catch(e) {
        console.error('Update failed:', e);
    }
}

setInterval(updateDashboard, 5000);
updateDashboard();
</script>
</body>
</html>"""

# ====================== ROUTES ======================

@app.route('/')
def dashboard():
    return DASHBOARD_HTML


@app.route('/api/status')
def api_status():
    return jsonify(dashboard_data)


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
        "status": "healthy",
        "scanner_running": True,
        "market_open": dashboard_data.get("market_open", False),
        "time": datetime.now().strftime("%H:%M:%S"),
    })


@app.route('/test-alert')
def test_alert():
    send_discord_alert(
        dashboard_data.get("price", 500),
        dashboard_data.get("score", 8),
        "🧪 MANUAL TEST ALERT"
    )
    return jsonify({"status": "success", "message": "Discord alert sent"})


# ====================== SMC HELPERS ======================

def detect_fvg(df):
    try:
        bullish = (df['Low'].shift(-1) > df['High'].shift(2)).iloc[-1]
        bearish = (df['High'].shift(-1) < df['Low'].shift(2)).iloc[-1]
        return bool(bullish or bearish)
    except Exception:
        return False


def detect_order_blocks(df):
    try:
        ob_bull = (df['Low'].rolling(10).min() == df['Low']).iloc[-1]
        ob_bear = (df['High'].rolling(10).max() == df['High']).iloc[-1]
        return bool(ob_bull or ob_bear)
    except Exception:
        return False


# ====================== MAIN SCANNER ======================

async def main():
    print("MAIN FUNCTION STARTED", flush=True)
    if not POLYGON_API_KEY:
        print("ERROR: POLYGON_API_KEY not set", flush=True)
        return

    client = RESTClient(POLYGON_API_KEY)
    print("Polygon client initialized", flush=True)
    print("✅ Scanner Engine Running", flush=True)

    while True:
        print("SCANNER LOOP RUNNING", flush=True)
        try:
            market_open = is_market_open()
            dashboard_data["market_open"] = market_open

            print(
                f"Fetching market data... (market {'OPEN' if market_open else 'CLOSED'})",
                flush=True
            )

            end   = datetime.now(timezone.utc)
            start = end - timedelta(days=5)

            aggs = list(itertools.islice(client.get_aggs(
                ticker="SPY",
                multiplier=1,
                timespan="minute",
                from_=start.strftime("%Y-%m-%d"),
                to=end.strftime("%Y-%m-%d"),
                limit=500
            ), 500))

            print(f"Fetched candles: {len(aggs)}", flush=True)

            if len(aggs) < 50:
                print("⚠️ Not enough candle data", flush=True)
                dashboard_data["status"] = "MARKET_CLOSED" if not market_open else "NO_DATA"
                await asyncio.sleep(300 if not market_open else 30)
                continue

            # Build dataframe with timestamps
            df = pd.DataFrame([{
                'Open':   a.open,
                'High':   a.high,
                'Low':    a.low,
                'Close':  a.close,
                'Volume': a.volume,
                'ts':     a.timestamp,
            } for a in aggs])

            df['date'] = pd.to_datetime(df['ts'], unit='ms', utc=True).dt.date

            # Indicators on full dataset
            df['sma20'] = ta.sma(df['Close'], length=20)
            df['rsi']   = ta.rsi(df['Close'], length=14)

            adx_df = ta.adx(df['High'], df['Low'], df['Close'], length=14)
            df['adx'] = adx_df['ADX_14']

            st_df = ta.supertrend(df['High'], df['Low'], df['Close'], length=7, multiplier=1.0)
            df['supertrend'] = st_df.iloc[:, 0]

            # VWAP on last trading day only (resets each session)
            last_day = df['date'].iloc[-1]
            day_df   = df[df['date'] == last_day].copy().reset_index(drop=True)
            if len(day_df) >= 5:
                day_df.index = pd.to_datetime(
                    day_df['ts'], unit='ms', utc=True
                ).dt.tz_convert('America/New_York')
                vwap_series = ta.vwap(day_df['High'], day_df['Low'], day_df['Close'], day_df['Volume'])
                vwap_val = vwap_series.iloc[-1] if (vwap_series is not None and len(vwap_series) > 0) else None
            else:
                vwap_val = None

            df = df.bfill()

            # Heikin Ashi
            ha_close = (df['Open'] + df['High'] + df['Low'] + df['Close']) / 4
            ha_open  = ha_close.shift(1)
            ha_bull  = bool(ha_close.iloc[-1] > ha_open.iloc[-1])

            # FTFC
            ftfc = (df['Close'] > df['Open']).rolling(30).mean().iloc[-1]

            # SMC
            fvg_active = detect_fvg(df)
            ob_active  = detect_order_blocks(df)

            # Extract latest values
            current_price = df['Close'].iloc[-1]
            sma20_val     = df['sma20'].iloc[-1]
            adx_val       = df['adx'].iloc[-1]
            rsi_val       = df['rsi'].iloc[-1]
            st_val        = df['supertrend'].iloc[-1]

            # Signal conditions
            sma20_active = _valid(sma20_val) and current_price > sma20_val
            adx_active   = _valid(adx_val)   and adx_val > 22
            rsi_active   = _valid(rsi_val)   and 45 < rsi_val < 65
            ftfc_active  = _valid(ftfc)      and ftfc > 0.6
            st_active    = _valid(st_val)    and current_price > st_val
            vwap_active  = _valid(vwap_val)  and current_price > vwap_val

            # Score (max 11)
            score  = 0
            score += 2 if sma20_active else 0
            score += 1 if adx_active   else 0
            score += 1 if rsi_active   else 0
            score += 2 if ftfc_active  else 0
            score += 1 if st_active    else 0
            score += 1 if ha_bull      else 0
            score += 1 if vwap_active  else 0
            score += 1 if fvg_active   else 0
            score += 1 if ob_active    else 0

            if not market_open:
                gov_status = "MARKET_CLOSED"
            elif score >= 8:
                gov_status = "NORMAL"
            else:
                gov_status = "REDUCED_RISK"

            signals = {
                "sma20":       {"value": f"{sma20_val:.2f}" if _valid(sma20_val) else "--", "active": bool(sma20_active), "label": "Above SMA20",  "points": 2},
                "adx":         {"value": f"{adx_val:.1f}"   if _valid(adx_val)   else "--", "active": bool(adx_active),   "label": "ADX > 22",     "points": 1},
                "rsi":         {"value": f"{rsi_val:.1f}"   if _valid(rsi_val)   else "--", "active": bool(rsi_active),   "label": "RSI 45-65",    "points": 1},
                "ftfc":        {"value": f"{ftfc*100:.0f}%" if _valid(ftfc)      else "--", "active": bool(ftfc_active),  "label": "FTFC > 60%",   "points": 2},
                "supertrend":  {"value": f"{st_val:.2f}"    if _valid(st_val)    else "--", "active": bool(st_active),    "label": "SuperTrend",   "points": 1},
                "heikin_ashi": {"value": "Bull" if ha_bull else "Bear",                     "active": bool(ha_bull),      "label": "Heikin Ashi",  "points": 1},
                "vwap":        {"value": f"{vwap_val:.2f}"  if _valid(vwap_val)  else "--", "active": bool(vwap_active),  "label": "Above VWAP",   "points": 1},
                "fvg":         {"value": "Active" if fvg_active else "None",                "active": bool(fvg_active),   "label": "FVG Active",   "points": 1},
                "ob":          {"value": "Active" if ob_active  else "None",                "active": bool(ob_active),    "label": "Order Block",  "points": 1},
            }

            history = dashboard_data["history"]
            history.append({"time": datetime.now().strftime("%H:%M"), "score": int(score)})
            if len(history) > 60:
                history.pop(0)
            save_history(history)

            dashboard_data.update({
                "price":       round(float(current_price), 2),
                "score":       int(score),
                "status":      gov_status,
                "last_update": datetime.now().strftime("%H:%M:%S"),
                "market_open": market_open,
                "signals":     signals,
                "history":     history,
            })

            if market_open and score >= 9:
                send_discord_alert(current_price, score, "🔥 HIGH CONFLUENCE SETUP")

            print(
                f"[{datetime.now().strftime('%H:%M:%S')}] "
                f"SPY {current_price:.2f} | Score: {score}/{MAX_SCORE} | {gov_status}",
                flush=True
            )

            # Poll less often when market is closed
            await asyncio.sleep(300 if not market_open else 45)

        except Exception:
            print("========== SCANNER ERROR ==========", flush=True)
            traceback.print_exc()
            await asyncio.sleep(15)


# ====================== START ======================
# Start scanner thread at module level so gunicorn picks it up
threading.Thread(
    target=lambda: asyncio.run(main()),
    daemon=True
).start()

if __name__ == "__main__":
    app.run(host='0.0.0.0', port=8080, debug=False)
