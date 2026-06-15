from flask import Flask, request, jsonify
import json
import os

app = Flask(__name__)

@app.route('/signal', methods=['POST'])
def receive_signal():
    data = request.get_json()
    print("🚨 SIGNAL RECEIVED:", data)
    
    # Save to file for MT5 EA to read
    with open('/tmp/axi_signal.json', 'w') as f:
        json.dump(data, f)
    
    return jsonify({"status": "received"})

if __name__ == "__main__":
    app.run(host='0.0.0.0', port=5000, debug=False)
