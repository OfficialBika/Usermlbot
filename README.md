# Usermlbot

A Pyrogram-based Telegram userbot with human-chat sessions, optional auto-catch/forward features, optional read-only MongoDB lookup, and an optional captcha solver.

## VPS requirements

- Ubuntu 24.04 LTS (or a compatible Linux distribution).
- Python 3.12 recommended for the Ubuntu 24.04 VPS.
- Git and a Python virtual environment.
- Telegram API ID/hash and two Pyrogram string sessions (A and B).
- Owner Telegram user ID and at least one monitored group ID.
- Optional: MongoDB URI/database only if Direct DB Catch is enabled.
- Optional: `tesseract-ocr` system package for Tesseract OCR fallback.

The repository CI checks Python syntax and source-level regression contracts on Python 3.11 and 3.12. The VPS guide below uses Python 3.12, which is the native Python version on Ubuntu 24.04. Avoid using an experimental Python version for production until all native dependencies (especially PyTorch/EasyOCR and TgCrypto) have compatible wheels.

## 1. Prepare the VPS

The commands below assume:
- Linux account: `bika`
- Project directory: `/home/bika/Usermlbot`
- Virtual environment: `/home/bika/Usermlbot/.venv`

Change the account and paths if your VPS uses a different layout.

```bash
sudo apt update
sudo apt install -y git python3.12 python3.12-venv python3-pip tesseract-ocr
sudo -u bika -H bash
cd /home/bika
git clone https://github.com/OfficialBika/Usermlbot.git
cd Usermlbot
python3.12 -m venv .venv
source .venv/bin/activate
python -m pip install --upgrade pip wheel
python -m pip install -r requirements.txt
```

If the repository is already cloned, do not clone it again. Enter the existing project directory and continue from virtual-environment setup.

## 2. Configure credentials

```bash
cp .env.example .env
nano .env
chmod 600 .env
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

Never commit or share `.env`, session strings, API hash, MongoDB URI, OTPs, or 2FA passwords. The root `config.json.example` is a legacy reference; the current application uses `.env.example`.

### Safe feature defaults

The example keeps optional automation disabled:

- `AUTO_FORWARD_ENABLED=false`
- `DIRECT_DB_CATCH_ENABLED=false`
- `CAPTCHA_SOLVER_ENABLED=false`
- `CAPTCHA_AUTO_APPROVE=false`

Enable optional features only after their IDs, target groups, sources, and behavior have been checked. Keep captcha auto-approval disabled unless solver accuracy and risk controls have been validated.

### Session behavior

- Session A and B are required; sessions C through H are optional.
- `HUMAN_CHAT_SESSIONS` can include any configured sessions from `a` through `h`.
- `AUTO_CATCH_SESSIONS` can include any configured sessions from `a` through `h`.
- Captcha solver and direct-DB catch session settings intentionally remain limited to A/B.

### Auto-forward requirements

When `AUTO_FORWARD_ENABLED=true` and `DIRECT_DB_CATCH_ENABLED=false`, configure the source and responder:

```env
BOT_ID=123456789
RESPONDER_BOT_ID=123456789
```

For SenpaiCatcher-only forwarding, `BOT_ID` is optional because the source ID defaults to `8532697507`:

```env
SENPAI_CATCHER_BOT_ID=8532697507
RESPONDER_BOT_ID=123456789
```

SenpaiCatcher spawn messages are forwarded to the configured responder, and complete `/pick` commands returned by that bot are sent to the original group. The feature uses the same enabled source groups, pending-response tracking, and A-H session handlers as the existing forward flow. SenpaiCatcher ignores all Rarity on/off toggles and forwards every recognized spawn; the existing Rarity filter remains unchanged for CatchBot and other sources. `RESPONDER_BOT_IDS` may be used for multiple responder bots. Direct DB Catch requires a MongoDB URI and database name. Its MongoDB connection is intended for read-only lookup; the bot does not create indexes or write application documents to that database.

#### Sharing the current Adding-Helperbot database

For the current Adding-Helperbot unified schema, configure Usermlbot's own `.env` with:

```env
DIRECT_DB_CATCH_ENABLED=true
DIRECT_DB_LAYOUT=adding_helperbot
DIRECT_DB_NAME=the_same_DB_NAME_used_by_Adding-Helperbot
DIRECT_DB_COLLECTION=characters
DIRECT_DB_SUPPORT_BOTS_COLLECTION=auto
DIRECT_DB_USE_DEFAULT_SOURCE_COLLECTIONS=true
```

Use the same MongoDB connection URI as Adding-Helperbot (either `DIRECT_DB_MONGO_URI` or Usermlbot's existing `MONGO_URI`). Do not paste credentials into chat or commit them. `DIRECT_DB_NAME` must exactly match Adding-Helperbot's live `DB_NAME`; check its local `.env` because repository examples may differ.

In this layout, Usermlbot reads the shared `characters` collection and scopes every match by Adding-Helperbot's `source_key` (for example, `items_character_catcher`). It checks the full `file_unique_ids` array first, with scalar legacy UID fields as compatibility fallbacks. Keep the built-in Source Collections map enabled so sender usernames resolve to the correct source key. MongoDB is strictly read-only: this bot only pings the server and performs `find` / `find_one` queries. It must never insert, update, replace, delete, create indexes, change metadata, or migrate MongoDB data. Use a MongoDB account granted only the `read` role for this database as an additional server-side safeguard.

All bot-owned runtime state—including `/auth` and `/unauth` permissions—is stored on the VPS filesystem in `bot_config.json` under `DATA_DIR` (default `./data`), not in MongoDB. Keep `DATA_DIR` on persistent VPS storage and back it up. SQLite catch history and captcha templates also remain local under `DATA_DIR`.

Leave `DIRECT_DB_LAYOUT=legacy` (the default) for the older per-source `items_*` collection layout.

## 3. Test manually before systemd

Run from the project directory with the virtual environment active:

```bash
cd /home/bika/Usermlbot
source .venv/bin/activate
python -m compileall -q main.py
python main.py
```

Confirm both required Telegram sessions connect and the startup summary is delivered. Press Ctrl+C once and confirm the process exits cleanly. Do not enable the systemd service until this manual test succeeds.

## 4. Install and run with systemd

The committed `usermlbot.service` is configured for the example account and path above. Verify that the Linux account exists and owns the project files:

```bash
id bika
sudo chown -R bika:bika /home/bika/Usermlbot
chmod 600 /home/bika/Usermlbot/.env
```

Install and start:

```bash
sudo cp /home/bika/Usermlbot/usermlbot.service /etc/systemd/system/usermlbot.service
sudo systemd-analyze verify /etc/systemd/system/usermlbot.service
sudo systemctl daemon-reload
sudo systemctl enable --now usermlbot
sudo systemctl status usermlbot --no-pager
```

View live logs:

```bash
sudo journalctl -u usermlbot -f
```

Useful service commands:

```bash
sudo systemctl restart usermlbot
sudo systemctl stop usermlbot
sudo systemctl start usermlbot
sudo systemctl is-enabled usermlbot
```

The service runs as the unprivileged `bika` account, restarts after unexpected failures, and sends SIGINT on stop so Python's asyncio runner can execute the application's graceful cleanup. Keep `DATA_DIR`, `.env`, and the virtual environment accessible to that account.

## 5. Update safely

Back up runtime state before updating:

```bash
sudo systemctl stop usermlbot
cd /home/bika/Usermlbot
mkdir -p /home/bika/backups
tar -czf /home/bika/backups/usermlbot-data-$(date +%F-%H%M%S).tar.gz data
git pull --ff-only
source .venv/bin/activate
python -m pip install -r requirements.txt
python -m compileall -q main.py
sudo systemctl start usermlbot
sudo systemctl status usermlbot --no-pager
```

If the service does not start, inspect:

```bash
sudo journalctl -u usermlbot -n 200 --no-pager
```

Do not delete `data/`, `catch_history.db`, or `bot_config.json` during updates; they contain runtime state and history.

## Persistent files

By default, runtime settings are stored in `bot_config.json` and history/template records in `catch_history.db`. Both are placed under `DATA_DIR` (default: `./data`). You can set an absolute persistent directory with `DATA_DIR` and override filenames with `BOT_CONFIG_FILE` and `DB_FILE`.

The project directory and `DATA_DIR` must be writable by the service account. Back up `data/` regularly and keep backups outside the repository directory.

## Security notes

- Generate Pyrogram sessions on a trusted device or your own VPS.
- Treat session strings as passwords: anyone with a valid session may access the Telegram account.
- Never share OTPs, 2FA passwords, API hashes, session strings, or MongoDB credentials.
- Keep auto-click and auto-forward features disabled until individually tested.
- Do not run multiple instances against the same sessions and SQLite database.

## Commands

Send owner commands from the configured owner account in an allowed chat. The owner can grant or revoke the limited group-loop permission with `/auth USER_ID` and `/unauth USER_ID`, or by replying to a user's message with either command. Authorized users can only run `/open` and `/close` in allowed groups; all other administrative commands remain owner-only. Authorization is persisted in `bot_config.json` across restarts. Use `/help` in Telegram for the runtime command list.
