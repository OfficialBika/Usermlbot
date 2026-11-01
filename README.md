# Usermlbot

A Pyrogram-based Telegram userbot with human-chat sessions, optional auto-catch/forward features, optional read-only MongoDB lookup, and an optional captcha solver.

## Requirements

- Python 3.10 or newer (Python 3.11 is used by the Render Blueprint).
- A Telegram API ID and API hash from Telegram.
- Two Pyrogram string sessions (Session A and Session B).
- Owner Telegram user ID and at least one monitored group ID.
- Optional: MongoDB URI/database if Direct DB Catch is enabled.

## Configuration

Create your environment file from the committed template:

```bash
cp .env.example .env
nano .env
```

Fill in the required values:

```env
API_ID=12345678
API_HASH=your_api_hash
SESSION_A_STRING=your_session_a_string
SESSION_B_STRING=your_session_b_string
OWNER_IDS=123456789
GROUP_IDS=-1001234567890
```

Never commit your real `.env`, session strings, API hash, MongoDB URI, or other credentials.

### Safe defaults

The example keeps optional automation disabled:

- `AUTO_FORWARD_ENABLED=false`
- `DIRECT_DB_CATCH_ENABLED=false`
- `CAPTCHA_SOLVER_ENABLED=false`
- `CAPTCHA_AUTO_APPROVE=false`

Enable each feature only after its required IDs, target groups, source configuration, and behavior have been verified. Captcha auto-approval should remain disabled unless you have validated solver accuracy and risk controls.

### Session behavior

- Session A and B are required.
- Session C and D are optional and intended for human-chat use.
- `HUMAN_CHAT_SESSIONS` can include `a,b,c,d`.
- Auto-catch and captcha solver session settings intentionally allow only A/B.

### Auto-forward requirements

When `AUTO_FORWARD_ENABLED=true` and `DIRECT_DB_CATCH_ENABLED=false`, configure:

```env
BOT_ID=123456789
RESPONDER_BOT_ID=123456789
```

Alternatively, use `RESPONDER_BOT_IDS` for multiple responder bots. When Direct DB Catch is enabled, configure a MongoDB URI and database name as well.

Direct DB Catch uses MongoDB as a read-only lookup source. The bot does not create indexes or write application documents to that database.

## Install on Ubuntu VPS

```bash
sudo apt update
sudo apt install -y python3 python3-venv python3-pip git
git clone https://github.com/OfficialBika/Usermlbot.git
cd Usermlbot
python3 -m venv .venv
source .venv/bin/activate
python -m pip install --upgrade pip
pip install -r requirements.txt
cp .env.example .env
nano .env
python main.py
```

Keep the `.venv`, `.env`, `data/`, and database files in the deployment directory. The application creates its data directory when it starts.

## Render deployment

The repository includes `render.yaml` with:

- Web service start command: `python main.py`
- Health check path: `/health`
- Bind address: `0.0.0.0`
- Port: Render-provided `PORT` (fallback 10000 for local use)

Set all required Telegram credentials and IDs in Render's environment settings. Do not place secrets in `render.yaml`.

**Production warning:** the current Blueprint selects Render's Free web-service plan. Free web services spin down after 15 minutes without inbound traffic, and their local filesystem is ephemeral; SQLite history and runtime config can be lost when the service spins down, restarts, or redeploys. This makes the Free plan unsuitable for a continuously connected Telegram userbot. Use an always-on VPS or a paid Render instance with persistent storage instead. [Render Free instance limitations](https://render.com/docs/free).

The health endpoint returns HTTP 200 only after both required Telegram sessions are connected. It returns HTTP 503 while starting or if either required session is disconnected. Render deployment and live health still need to be verified in the Render dashboard after pushing changes.

## systemd deployment

The included `usermlbot.service` is a deployment template. Replace every `REPLACE_...` value and project path before installing. The example assumes the project uses a `.venv` virtual environment:

```ini
User=bika
Group=bika
WorkingDirectory=/home/bika/Usermlbot
EnvironmentFile=/home/bika/Usermlbot/.env
ExecStart=/home/bika/Usermlbot/.venv/bin/python -u /home/bika/Usermlbot/main.py
```

Create the Linux account and ensure it owns the project directory, `.env`, and the configured `DATA_DIR`. Do not leave the placeholder values in the installed unit. Then install and start:

```bash
sudo cp usermlbot.service /etc/systemd/system/usermlbot.service
sudo nano /etc/systemd/system/usermlbot.service
sudo systemd-analyze verify /etc/systemd/system/usermlbot.service
sudo systemctl daemon-reload
sudo systemctl enable --now usermlbot
sudo systemctl status usermlbot
journalctl -u usermlbot -f
```

If your venv is named `venv` instead of `.venv`, update `ExecStart` accordingly.

## Persistent files

By default, runtime settings are stored in `bot_config.json` and history/template records in `catch_history.db`. You can move both into a persistent directory using `DATA_DIR`, and override the filenames with `BOT_CONFIG_FILE` and `DB_FILE`.

For Render, note that filesystem persistence depends on the service's configured persistent disk. Without persistent storage, local SQLite history and saved auto-config may be lost on instance replacement or redeploy. Configure a disk and a matching `DATA_DIR` before relying on local persistence.

## Security notes

- Generate Pyrogram sessions on a trusted device or your own VPS.
- Treat session strings as passwords: anyone with a valid session may access the Telegram account.
- Never share OTPs, 2FA passwords, API hashes, session strings, or MongoDB credentials.
- Keep auto-click and auto-forward features disabled until individually tested.

## Commands

Send supported owner commands from the configured owner account in an allowed chat. Use `/help` in Telegram for the runtime command list.
