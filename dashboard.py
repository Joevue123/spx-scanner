import pandas as pd
from datetime import datetime
import json
import os

class RiskDashboard:
    def __init__(self):
        self.equity = 500.0
        self.peak_equity = 500.0
        self.daily_pnl = 0.0
        self.trade_count_today = 0
        self.today = datetime.now().date()
        self.history = []

    def update(self, current_equity, governance_status, score):
        if datetime.now().date() != self.today:
            self.daily_pnl = 0.0
            self.trade_count_today = 0
            self.today = datetime.now().date()

        self.equity = current_equity
        if self.equity > self.peak_equity:
            self.peak_equity = self.equity

        drawdown = (self.peak_equity - self.equity) / self.peak_equity * 100 if self.peak_equity > 0 else 0

        self.history.append({
            'time': datetime.now().strftime('%H:%M:%S'),
            'equity': current_equity,
            'drawdown': drawdown,
            'governance': governance_status,
            'confluence': score
        })

        self.print_dashboard(governance_status, score)

    def print_dashboard(self, governance_status, score):
        os.system('clear')
        print('='*60)
        print(f'SPX SCANNER RISK DASHBOARD - {datetime.now().strftime("%Y-%m-%d %H:%M:%S")}')
        print('='*60)
        print(f'Current Equity     : ${self.equity:.2f}')
        print(f'Peak Equity        : ${self.peak_equity:.2f}')
        print(f'Current Drawdown   : {(self.peak_equity - self.equity) / self.peak_equity * 100:.2f}%')
        print(f'Daily PnL          : ${self.daily_pnl:.2f}')
        print(f'Trades Today       : {self.trade_count_today}')
        print(f'Governance Status  : {governance_status}')
        print(f'Confluence Score   : {score}/10')
        print('-'*60)
        print('Recent History:')
        for entry in self.history[-5:]:
            print(f'  {entry["time"]} | DD: {entry["drawdown"]:5.2f}% | Score: {entry["confluence"]} | {entry["governance"]}')
        print('='*60)

dashboard = RiskDashboard()
