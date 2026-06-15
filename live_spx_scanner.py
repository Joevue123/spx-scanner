import asyncio
import traceback
import pandas as pd
import pandas_ta as ta
import requests
from datetime import datetime, timedelta, timezone
from polygon import RESTClient
from flask import Flask, render_template_string, jsonify
import threading
import os

# ====================== CONFIG ======================
POLYGON_API_KEY = os.getenv("POLYGON_API_KEY")
DISCORD_WEBHOOK = os.getenv("DISCORD_WEBHOOK")

print("=== FULL SPX CONFLUENCE SCANNER STARTING ===")

# ====================== FLASK ======================
app = Flask(__name__)

dashboard_data = {
    "price": 0.0,
    "score": 0,
    "status": "STARTING",
    "last_update": "N/A"
}

# ====================== DISCORD ALERTS ======================
def send_discord_alert(price, score, message="Strong Signal"):
    if not DISCORD_WEBHOOK:
        print("Discord webhook not configured")
        return

    try:
        payload = {
            "content": (
                f"🚨 **SPY Scanner Alert** 🚨\n"
                f"**Price:** {price:.2f}\n"
                f"**Score:** {score}/10\n"
                f"**Signal:** {message}\n"
                f"**Time:** {datetime.now().strftime('%H:%M:%S')}"
            )
        }

        requests.post(
            DISCORD_WEBHOOK,
            json=payload,
            timeout=5
        )

        print("✅ Discord alert sent")

    except Exception as e:
        print(f"Discord failed: {e}")

# ====================== DASHBOARD ======================
@app.route('/')
def dashboard():

    html = """
    <!DOCTYPE html>
    <html lang="en">
    <head>
        <meta charset="UTF-8">
        <meta name="viewport"
              content="width=device-width, initial-scale=1.0">

        <title>SPY Confluence Scanner</title>

        <link href="https://cdn.jsdelivr.net/npm/bootstrap@5.3.3/dist/css/bootstrap.min.css"
              rel="stylesheet">

        <style>
            body {
                background: #0a0a0a;
                color: #00ff88;
                font-family: 'Segoe UI', sans-serif;
            }

            .card {
                background: #111;
                border: 1px solid #00ff88;
            }

            .price {
                font-size: 3rem;
                font-weight: bold;
                color: #00ffcc;
            }

            .status-normal {
                color: #00ff88;
            }

            .status-risk {
                color: #ff4444;
            }
        </style>
    </head>

    <body class="p-4">

        <div class="container">

            <h1 class="text-center mb-4 text-success">
                🚀 SPY Full Confluence Scanner
            </h1>

            <div class="row">

                <div class="col-md-5">

                    <div class="card p-4 mb-3">

                        <h4>Live Status</h4>

                        <div class="price" id="price">0.00</div>

                        <p>
                            Score:
                            <strong id="score">0/10</strong>
                        </p>

                        <p>
                            Status:
                            <strong id="status">STARTING</strong>
                        </p>

                        <small>
                            Last Updated:
                            <span id="last_update">N/A</span>
                        </small>

                    </div>

                </div>

                <div class="col-md-7">

                    <div class="card p-3">

                        <h5>SPY Live Chart</h5>

                        <iframe
                            src="https://www.tradingview.com/widgetembed/?symbol=AMEX:SPY&interval=1&theme=dark"
                            width="100%"
                            height="520"
                            frameborder="0">
                        </iframe>

                    </div>

                </div>

            </div>

        </div>

        <script>

            async function updateDashboard() {

                try {

                    const response = await fetch('/api/status');

                    const data = await response.json();

                    document.getElementById('price').textContent =
                        parseFloat(data.price).toFixed(2);

                    document.getElementById('score').textContent =
                        data.score + '/10';

                    document.getElementById('status').textContent =
                        data.status;

                    document.getElementById('last_update').textContent =
                        data.last_update;

                } catch(error) {

                    console.log("Dashboard update failed:", error);

                }
            }

            // update every 5 seconds
            setInterval(updateDashboard, 5000);

            updateDashboard();

        </script>

    </body>
    </html>
    """

    return render_template_string(html)

# ====================== API ======================
@app.route('/api/status')
def api_status():
    return jsonify(dashboard_data)

@app.route('/health')
def health():
    return jsonify({
        "status": "healthy",
        "scanner_running": True,
        "time": datetime.now().strftime("%H:%M:%S")
    })

@app.route('/test-alert')
def test_alert():

    send_discord_alert(
        dashboard_data.get("price", 500),
        dashboard_data.get("score", 8),
        "🧪 MANUAL TEST ALERT"
    )

    return jsonify({
        "status": "success",
        "message": "Discord alert sent"
    })

# ====================== SMC HELPERS ======================
def detect_fvg(df):

    try:
        bullish = (
            df['Low'].shift(-1) >
            df['High'].shift(2)
        ).iloc[-1]

        bearish = (
            df['High'].shift(-1) <
            df['Low'].shift(2)
        ).iloc[-1]

        return bullish or bearish

    except:
        return False

def detect_order_blocks(df):

    try:
        ob_bull = (
            df['Low'].rolling(10).min() ==
            df['Low']
        ).iloc[-1]

        ob_bear = (
            df['High'].rolling(10).max() ==
            df['High']
        ).iloc[-1]

        return ob_bull or ob_bear

    except:
        return False

# ====================== MAIN SCANNER ======================
async def main():
    print("MAIN FUNCTION STARTED")
    if not POLYGON_API_KEY:
        print("❌ ERROR: POLYGON_API_KEY not set")
        return

    client = RESTClient(POLYGON_API_KEY)
    print("Polygon client initialized")
    print("✅ Scanner Engine Running")

    while True:
        print("SCANNER LOOP RUNNING")

        try:

            print("Fetching market data...")

            # ======================
            # FETCH DATA
            # ======================

            end = datetime.now(timezone.utc)
            start = end - timedelta(days=2)

            aggs = list(client.get_aggs(
                ticker="SPY",
                multiplier=1,
                timespan="minute",
                from_=start.strftime("%Y-%m-%d"),
                to=end.strftime("%Y-%m-%d"),
                limit=300
            ))

            print(f"Fetched candles: {len(aggs)}")

            if len(aggs) < 50:
                print("⚠️ Not enough candle data")
                await asyncio.sleep(30)
                continue

            # ======================
            # DATAFRAME
            # ======================

            df = pd.DataFrame([{
                'Open': a.open,
                'High': a.high,
                'Low': a.low,
                'Close': a.close,
                'Volume': a.volume
            } for a in aggs])

            # ======================
            # INDICATORS
            # ======================

            df['sma20'] = ta.sma(df['Close'], length=20)

            df['rsi'] = ta.rsi(df['Close'], length=14)

            adx = ta.adx(
                df['High'],
                df['Low'],
                df['Close'],
                length=14
            )

            df['adx'] = adx['ADX_14']

            # ======================
            # SUPERTREND FIX
            # ======================

            supertrend = ta.supertrend(
                df['High'],
                df['Low'],
                df['Close'],
                length=7,
                multiplier=1.0
            )

            df['supertrend'] = supertrend.iloc[:, 0]

            # ======================
            # HEIKIN ASHI FIX
            # ======================

            ha_close = (
                df['Open'] +
                df['High'] +
                df['Low'] +
                df['Close']
            ) / 4

            ha_open = ha_close.shift(1)

            ha_bull = (
                ha_close.iloc[-1] >
                ha_open.iloc[-1]
            )

            # ======================
            # VWAP
            # ======================

            df['vwap'] = ta.vwap(
                df['High'],
                df['Low'],
                df['Close'],
                df['Volume']
            )

            # ======================
            # CLEAN NAN
            # ======================

            df = df.fillna(method='bfill')

            # ======================
            # FTFC
            # ======================

            ftfc = (
                (df['Close'] > df['Open'])
                .rolling(30)
                .mean()
                .iloc[-1]
            )

            # ======================
            # SMC FEATURES
            # ======================

            fvg_active = detect_fvg(df)

            ob_active = detect_order_blocks(df)

            # ======================
            # SCORE ENGINE
            # ======================

            score = 0

            current_price = df['Close'].iloc[-1]

            score += 2 if current_price > df['sma20'].iloc[-1] else 0

            score += 1 if df['adx'].iloc[-1] > 22 else 0

            score += 1 if 45 < df['rsi'].iloc[-1] < 65 else 0

            score += 2 if ftfc > 0.6 else 0

            score += 1 if current_price > df['supertrend'].iloc[-1] else 0

            score += 1 if ha_bull else 0

            score += 1 if current_price > df['vwap'].iloc[-1] else 0

            score += 1 if fvg_active else 0

            score += 1 if ob_active else 0

            # ======================
            # STATUS
            # ======================

            gov_status = (
                "NORMAL"
                if score >= 7
                else "REDUCED_RISK"
            )

            # ======================
            # UPDATE DASHBOARD
            # ======================

            dashboard_data.update({
                "price": round(float(current_price), 2),
                "score": int(score),
                "status": gov_status,
                "last_update": datetime.now().strftime("%H:%M:%S")
            })

            # ======================
            # ALERTS
            # ======================

            if score >= 8:

                send_discord_alert(
                    current_price,
                    score,
                    "🔥 HIGH CONFLUENCE SETUP"
                )

            print(
                f"[{datetime.now().strftime('%H:%M:%S')}] "
                f"SPY {current_price:.2f} | "
                f"Score: {score}/10 | "
                f"Status: {gov_status}"
            )

            # ======================
            # WAIT
            # ======================

            await asyncio.sleep(45)

        except Exception:

            print("========== SCANNER ERROR ==========")

            traceback.print_exc()

            await asyncio.sleep(15)

# ====================== START APP ======================
if __name__ == "__main__":

    threading.Thread(
        target=lambda: asyncio.run(main()),
        daemon=True
    ).start()

    app.run(
        host='0.0.0.0',
        port=8080,
        debug=False
    )
