FROM python:3.12-slim

WORKDIR /app

COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

COPY . .

EXPOSE 5000 8080

CMD ["sh", "-c", "python axi_webhook_bridge.py & gunicorn --bind 0.0.0.0:8080 --workers 1 --threads 4 --timeout 120 live_spx_scanner:app"]
