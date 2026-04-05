# MLBB Telegram Auto Chat (Production Ready)

## Files
- main.py
- config.json.example
- requirements.txt
- locales/sessa.txt
- locales/sessb.txt
- data/state.json
- logs/.gitkeep

## Setup
1. `pip install -r requirements.txt`
2. `cp config.json.example config.json`
3. Edit `config.json`
4. `python main.py`

## Commands
Use these commands from OWNER_ID in the target group only:
- /open
- /close
- /status
- /reload
- /help

## Current behavior
- The bot runs in one target group only (`group_id`)
- It works only while `/open` is enabled
- Session A sends -> Session B replies from `sessb.txt`
- If `enable_two_way=true`, Session B sends -> Session A replies from `sessa.txt`
- Replies are sequential, one line at a time
- Sent-line history is tracked so the same normalized line is not reused until the full file cycle finishes
- Safer default delay is `8` to `25` seconds

## Notes
- `session_a` and `session_b` are Pyrogram session file names, not session strings
- Keep `config.json` and generated `.session` files private
- Locale lines starting with `#` or blank lines are ignored

This package includes large locale files:
- locales/sessa.txt: 5200 lines
- locales/sessb.txt: 5200 lines
