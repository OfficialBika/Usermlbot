# Usermlbot VPS Env Version

This package is a VPS-ready version of the original `OfficialBika/Usermlbot` repo.

## What changed
- Removed `config.json`
- Uses environment variables only
- Uses Pyrogram `session_string` instead of `.session` files
- Keeps a simple `/health` endpoint in case you want to test locally or proxy it later
- Added `systemd` service file for Ubuntu VPS
- Added `run.sh` helper

## Requirements
- Ubuntu 22.04 / 24.04 VPS
- Python 3.10+
- Git
- A Telegram API ID and API hash
- Two Pyrogram string sessions

## Files
- `main.py` -> bot entrypoint
- `.env.example` -> environment variable template
- `run.sh` -> helper to start manually
- `usermlbot.service` -> systemd service example
- `locales/sessa.txt` and `locales/sessb.txt` -> reply text pools

## 1) Upload or clone to VPS
```bash
git clone https://github.com/OfficialBika/Usermlbot.git
cd Usermlbot
```

Then replace the repo files with the files from this package.

## 2) Install Python and create venv
```bash
sudo apt update
sudo apt install -y python3 python3-pip python3-venv git
python3 -m venv venv
source venv/bin/activate
pip install -r requirements.txt
```

## 3) Create `.env`
```bash
cp .env.example .env
nano .env
```

Fill in:
```env
API_ID=12345678
API_HASH=your_api_hash
SESSION_A_STRING=your_pyrogram_string_session_a
SESSION_B_STRING=your_pyrogram_string_session_b
OWNER_ID=123456789
GROUP_ID=-1001234567890
ENABLE_TWO_WAY=false
MIN_REPLY_DELAY=8
MAX_REPLY_DELAY=12
DEBUG=false
HOST=0.0.0.0
PORT=10000
```

## 4) Start manually for testing
```bash
source venv/bin/activate
export $(grep -v '^#' .env | xargs)
python main.py
```

## 5) Run with systemd
Edit the service file path first:
```bash
nano usermlbot.service
```

Make sure these match your VPS setup:
- `WorkingDirectory=/home/ubuntu/Usermlbot`
- `ExecStart=/home/ubuntu/Usermlbot/venv/bin/python /home/ubuntu/Usermlbot/main.py`
- `EnvironmentFile=/home/ubuntu/Usermlbot/.env`
- `User=ubuntu`

Install service:
```bash
sudo cp usermlbot.service /etc/systemd/system/usermlbot.service
sudo systemctl daemon-reload
sudo systemctl enable usermlbot
sudo systemctl start usermlbot
```

Check logs:
```bash
sudo systemctl status usermlbot
journalctl -u usermlbot -f
```

Restart after changes:
```bash
sudo systemctl restart usermlbot
```

## 6) Session strings
You said you will get string sessions from a Telegram bot and put them into env.
That is technically possible.

Use them like this in `.env`:
```env
SESSION_A_STRING=...
SESSION_B_STRING=...
```

## Important security warning
A third-party Telegram bot can steal or reuse:
- API ID / API hash
- phone number
- OTP code
- 2FA password
- generated string session

So if you use a Telegram bot to generate sessions, do it at your own risk.
The safer option is generating Pyrogram session strings yourself on your own VPS or PC.

## Bot commands
Send these in the target group from the owner account:
- `/open`
- `/close`
- `/status`
- `/help`

## Notes
- VPS is better than Render free web service for this repo
- Keep `locales/sessa.txt` and `locales/sessb.txt` filled with your reply lines
- Keep your `.env` private
