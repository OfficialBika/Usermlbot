import asyncio
import json
import logging
import os
import random
from logging.handlers import RotatingFileHandler
from typing import Dict, List, Optional, Set

from pyrogram import Client, filters, idle
from pyrogram.enums import ChatType, ChatAction
from pyrogram.errors import FloodWait, RPCError
from pyrogram.types import Message

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
CONFIG_FILE = os.path.join(BASE_DIR, "config.json")
STATE_FILE = os.path.join(BASE_DIR, "data", "state.json")
LOCALES_DIR = os.path.join(BASE_DIR, "locales")
SESSA_FILE = os.path.join(LOCALES_DIR, "sessa.txt")
SESSB_FILE = os.path.join(LOCALES_DIR, "sessb.txt")
LOG_DIR = os.path.join(BASE_DIR, "logs")
LOG_FILE = os.path.join(LOG_DIR, "bot.log")

EMOJIS = ["😂","😅","😆","😉","🔥","😎","😁","😄","🙂","🤭"]

DEFAULT_STATE = {
    "enabled": False,
    "sessa_index": 0,
    "sessb_index": 0,
    "sessa_history": [],
    "sessb_history": [],
}

session_a_id: Optional[int] = None
session_b_id: Optional[int] = None
sessa_lines: List[str] = []
sessb_lines: List[str] = []
recent_auto_messages = set()
message_lock = asyncio.Lock()
last_trigger = {"from_a": None, "from_b": None}
state: Dict[str, object] = DEFAULT_STATE.copy()

logger = logging.getLogger("auto-chat")

CONFIG: Dict[str, object] = {}
app_a: Optional[Client] = None
app_b: Optional[Client] = None


def read_json(path: str) -> Dict[str, object]:
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def setup_logging(debug: bool) -> None:
    os.makedirs(LOG_DIR, exist_ok=True)

    root = logging.getLogger()
    root.setLevel(logging.DEBUG if debug else logging.INFO)

    formatter = logging.Formatter("%(asctime)s | %(levelname)s | %(message)s")

    file_handler = RotatingFileHandler(LOG_FILE, maxBytes=2_000_000, backupCount=5, encoding="utf-8")
    file_handler.setFormatter(formatter)

    stream_handler = logging.StreamHandler()
    stream_handler.setFormatter(formatter)

    root.handlers.clear()
    root.addHandler(file_handler)
    root.addHandler(stream_handler)


def load_lines(path: str) -> List[str]:
    lines = []
    try:
        with open(path, "r", encoding="utf-8") as f:
            for raw in f:
                line = raw.strip()
                if line:
                    lines.append(line)
    except:
        pass
    return lines


def reload_locales() -> None:
    global sessa_lines, sessb_lines
    sessa_lines = load_lines(SESSA_FILE)
    sessb_lines = load_lines(SESSB_FILE)


def normalize_text(text: str) -> str:
    return (text or "").strip().lower()


def allowed_chat(message: Message) -> bool:
    if message.chat.id != CONFIG["group_id"]:
        return False
    return message.chat.type in {ChatType.GROUP, ChatType.SUPERGROUP}


async def ensure_me_ids() -> None:
    global session_a_id, session_b_id
    if session_a_id is None:
        session_a_id = (await app_a.get_me()).id
    if session_b_id is None:
        session_b_id = (await app_b.get_me()).id


def get_next_line(which: str):
    if which == "sessa":
        lines = sessa_lines
        key = "sessa_index"
    else:
        lines = sessb_lines
        key = "sessb_index"

    if not lines:
        return None

    idx = int(state.get(key, 0))
    line = lines[idx]
    idx = (idx + 1) % len(lines)
    state[key] = idx

    # add random emoji sometimes
    if random.random() < 0.4:
        line += " " + random.choice(EMOJIS)

    return line


async def send_message_smart(sender_app, chat_id, reply_to_id, text):
    try:
        delay = random.uniform(CONFIG["min_reply_delay"], CONFIG["max_reply_delay"])
        await asyncio.sleep(delay)

        # typing action
        await sender_app.send_chat_action(chat_id, ChatAction.TYPING)
        await asyncio.sleep(random.uniform(2, 4))

        # 70% plain, 30% reply
        if random.random() < 0.7:
            msg = await sender_app.send_message(chat_id, text)
        else:
            msg = await sender_app.send_message(chat_id, text, reply_to_message_id=reply_to_id)

        recent_auto_messages.add(msg.id)
        return msg

    except FloodWait as e:
        await asyncio.sleep(e.value)
    except RPCError as e:
        logger.error(e)


def register_handlers():
    @app_a.on_message(filters.text)
    async def commands(_, message: Message):
        if message.from_user.id != CONFIG["owner_id"]:
            return
        if message.text == "/open":
            state["enabled"] = True
            await message.reply("Auto ON")
        elif message.text == "/close":
            state["enabled"] = False
            await message.reply("Auto OFF")

    @app_a.on_message(filters.text)
    async def watch_a(_, message: Message):
        if not state["enabled"]:
            return
        if not allowed_chat(message):
            return

        await ensure_me_ids()

        if message.from_user.id == session_a_id:
            text = get_next_line("sessb")
            if text:
                await send_message_smart(app_b, CONFIG["group_id"], message.id, text)

    @app_b.on_message(filters.text)
    async def watch_b(_, message: Message):
        if not state["enabled"]:
            return
        if not allowed_chat(message):
            return

        await ensure_me_ids()

        if message.from_user.id == session_b_id:
            text = get_next_line("sessa")
            if text:
                await send_message_smart(app_a, CONFIG["group_id"], message.id, text)


async def main():
    global CONFIG, app_a, app_b

    CONFIG = read_json(CONFIG_FILE)
    setup_logging(CONFIG.get("debug", False))
    reload_locales()

    app_a = Client(CONFIG["session_a"], CONFIG["api_id"], CONFIG["api_hash"])
    app_b = Client(CONFIG["session_b"], CONFIG["api_id"], CONFIG["api_hash"])

    register_handlers()

    await app_a.start()
    await app_b.start()

    print("Bot Started")
    await idle()

    await app_a.stop()
    await app_b.stop()


if __name__ == "__main__":
    asyncio.run(main())
