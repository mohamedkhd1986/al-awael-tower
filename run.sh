#!/bin/bash
cd "$(dirname "$0")"
[ -d .venv ] || { python3 -m venv .venv && . .venv/bin/activate && pip install -r requirements.txt && playwright install chromium; }
. .venv/bin/activate; python app.py
