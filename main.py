import asyncio
import logging
import os
import random
import unicodedata
from typing import List, Optional

from dotenv import load_dotenv
from pyrogram import Client, filters, idle
from pyrogram.enums import ChatAction
from pyrogram.errors import FloodWait

load_dotenv()

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
LOCALES_DIR = os.path.join(BASE_DIR, "locales")
SESSA_FILE = os.path.join(LOCALES_DIR, "sessa.txt")
SESSB_FILE = os.path.join(LOCALES_DIR, "sessb.txt")

EMOJIS = ["🙂", "😄", "😉", "😎", "🔥", "✨", "😂", "🥰"]
OWNER_TAG = "@Official_Bika"

TRIGGER_EMOJIS = [
    "💮", "🟡", "🎴", "💈", "💊", "🎞", "✨", "🪞", "⚜️",
]

TRIGGER_KEYWORDS = [
    "captcha",
    "attention",
    "special",
]

app_a: Optional[Client] = None
app_b: Optional[Client] = None
session_a_id = None
session_b_id = None
sessa_lines: List[str] = []
sessb_lines: List[str] = []
enabled = False
conversation_task: Optional[asyncio.Task] = None
CONFIG = {}


def getenv_required(name: str) -> str:
    value = os.getenv(name)
    if value is None or value == "":
        raise RuntimeError(f"Missing required environment variable: {name}")
    return value


def getenv_bool(name: str, default: bool = False) -> bool:
    value = os.getenv(name)
    if value is None:
        return default
    return value.strip().lower() in {"1", "true", "yes", "y", "on"}


def getenv_int(name: str, default: int) -> int:
    value = os.getenv(name)
    if value is None or value == "":
        return default
    return int(value)

def getenv_float(name: str, default: float) -> float:
    value = os.getenv(name)
    if value is None or value == "":
        return default
    return float(value)

def load_config() -> dict:
    min_delay = getenv_int("MIN_REPLY_DELAY", 2)
    max_delay = getenv_int("MAX_REPLY_DELAY", 4)
    if min_delay > max_delay:
        min_delay, max_delay = max_delay, min_delay

    return {
        "api_id": int(getenv_required("API_ID")),
        "api_hash": getenv_required("API_HASH"),
        "session_a_string": getenv_required("SESSION_A_STRING"),
        "session_b_string": getenv_required("SESSION_B_STRING"),
        "owner_id": int(getenv_required("OWNER_ID")),
        "group_id": int(getenv_required("GROUP_ID")),
        "min_reply_delay": min_delay,
        "max_reply_delay": max_delay,
        "reply_chance": getenv_float("REPLY_CHANCE", 0.25),
        "debug": getenv_bool("DEBUG", False),
    }


def setup_logging(debug: bool) -> None:
    level = logging.DEBUG if debug else logging.WARNING
    logging.basicConfig(
        level=level,
        format="%(asctime)s | %(levelname)s | %(message)s",
        force=True,
    )
    logging.getLogger().setLevel(level)
    logging.getLogger("pyrogram").setLevel(logging.CRITICAL)
    logging.getLogger("asyncio").setLevel(logging.CRITICAL)


def load_lines(path: str) -> List[str]:
    try:
        with open(path, "r", encoding="utf-8") as f:
            lines = []
            for raw in f:
                line = raw.strip()
                if not line or line.startswith("#"):
                    continue
                lines.append(line)
            return lines
    except Exception as e:
        logging.warning("Failed to load %s: %s", path, e)
        return []


async def ensure_ids() -> None:
    global session_a_id, session_b_id
    if session_a_id is None:
        session_a_id = (await app_a.get_me()).id
    if session_b_id is None:
        session_b_id = (await app_b.get_me()).id


def get_text(which: str) -> str:
    pool = sessa_lines if which == "a" else sessb_lines
    if not pool:
        return random.choice(EMOJIS)

    text = random.choice(pool)
    if EMOJIS and random.random() < 0.5:
        text += " " + random.choice(EMOJIS)
    if EMOJIS and random.random() < 0.1:
        text = random.choice(EMOJIS)
    return text


def normalize_text(text: str) -> str:
    if not text:
        return ""

    text = unicodedata.normalize("NFKC", text).lower()
    fancy_map = str.maketrans({
        "ᴀ": "a", "ʙ": "b", "ᴄ": "c", "ᴅ": "d", "ᴇ": "e", "ғ": "f",
        "ɢ": "g", "ʜ": "h", "ɪ": "i", "ᴊ": "j", "ᴋ": "k", "ʟ": "l",
        "ᴍ": "m", "ɴ": "n", "ᴏ": "o", "ᴘ": "p", "ǫ": "q", "ʀ": "r",
        "ᴛ": "t", "ᴜ": "u", "ᴠ": "v", "ᴡ": "w", "ʏ": "y", "ᴢ": "z",
        "ꜱ": "s",
    })
    text = text.translate(fancy_map)

    cleaned = []
    for ch in text:
        if ch.isalnum() or ch.isspace():
            cleaned.append(ch)
        else:
            cleaned.append(" ")

    return " ".join("".join(cleaned).split())


def is_spawn_alert_message(m) -> bool:
    raw_text = m.text or ""
    raw_caption = m.caption or ""
    raw_content = f"{raw_text}\n{raw_caption}"

    has_trigger_emoji = any(emoji in raw_content for emoji in TRIGGER_EMOJIS)
    normalized = normalize_text(raw_content)
    has_trigger_keyword = any(keyword in normalized for keyword in TRIGGER_KEYWORDS)

    return has_trigger_emoji or has_trigger_keyword


async def send_owner_mention(app: Client, chat_id: int, reply_to: Optional[int] = None):
    text = OWNER_TAG
    try:
        if reply_to:
            return await app.send_message(chat_id, text, reply_to_message_id=reply_to)
        return await app.send_message(chat_id, text)
    except Exception as e:
        logging.warning("send_owner_mention failed: %s", e)
        return None


async def send_human(
    app: Client,
    chat_id: int,
    reply_to: Optional[int],
    text: str,
    force_reply: bool = False,
):
    try:
        await asyncio.sleep(random.uniform(CONFIG["min_reply_delay"], CONFIG["max_reply_delay"]))
        await app.send_chat_action(chat_id, ChatAction.TYPING)
        await asyncio.sleep(random.uniform(0.3, 0.8))

        use_reply = bool(reply_to) and (force_reply or random.random() < CONFIG["reply_chance"])

        if use_reply:
            try:
                return await app.send_message(
                    chat_id,
                    text,
                    reply_to_message_id=reply_to,
                )
            except Exception as e:
                logging.warning("reply send failed, fallback to normal message: %s", e)

        return await app.send_message(chat_id, text)

    except FloodWait as e:
        logging.warning("FloodWait: sleeping %s seconds", e.value)
        await asyncio.sleep(e.value)
        return None
    except Exception as e:
        logging.warning("send_human failed: %s", e)
        return None

async def conversation_loop():
    global enabled
    try:
        while enabled:
            msg_a = await send_human(app_a, CONFIG["group_id"], None, get_text("a"))
            if not msg_a:
                await asyncio.sleep(2)
                continue

            msg_b = await send_human(app_b, CONFIG["group_id"], msg_a.id, get_text("b"))
            if not msg_b:
                await asyncio.sleep(2)
                continue

            await send_human(app_a, CONFIG["group_id"], msg_b.id, get_text("a"))

    except asyncio.CancelledError:
        pass
    except Exception as e:
        logging.warning("conversation_loop failed: %s", e)


def register_handlers() -> None:
    @app_a.on_message(filters.chat(CONFIG["group_id"]) & filters.text)
    async def commands(_, m):
        global enabled, conversation_task
        try:
            if not m.from_user:
                return
            if m.from_user.id != CONFIG["owner_id"]:
                return

            if m.text == "/open":
                enabled = True
                await m.reply("✅ ON")

                if conversation_task and not conversation_task.done():
                    conversation_task.cancel()

                conversation_task = asyncio.create_task(conversation_loop())

            elif m.text == "/close":
                enabled = False
                await m.reply("❌ OFF")

                if conversation_task and not conversation_task.done():
                    conversation_task.cancel()

            elif m.text == "/status":
                running = bool(conversation_task and not conversation_task.done())
                await m.reply(
                    f"enabled={enabled}\n"
                    f"group_id={CONFIG['group_id']}\n"
                    f"loop_running={running}"
                )

            elif m.text == "/help":
                await m.reply("/open\n/close\n/status\n/help")

        except Exception as e:
            logging.warning("commands handler failed: %s", e)

    @app_a.on_message(filters.chat(CONFIG["group_id"]))
    async def detect_spawn_alert_a(_, m):
        try:
            is_bot_message = bool((m.from_user and m.from_user.is_bot) or m.sender_chat)
            if not is_bot_message:
                return
            if not is_spawn_alert_message(m):
                return
            await send_owner_mention(app_a, CONFIG["group_id"], m.id)
        except Exception as e:
            logging.warning("detect_spawn_alert_a failed: %s", e)

    @app_b.on_message(filters.chat(CONFIG["group_id"]))
    async def detect_spawn_alert_b(_, m):
        try:
            is_bot_message = bool((m.from_user and m.from_user.is_bot) or m.sender_chat)
            if not is_bot_message:
                return
            if not is_spawn_alert_message(m):
                return
            await send_owner_mention(app_b, CONFIG["group_id"], m.id)
        except Exception as e:
            logging.warning("detect_spawn_alert_b failed: %s", e)


async def main() -> None:
    global CONFIG, app_a, app_b, sessa_lines, sessb_lines

    CONFIG = load_config()
    setup_logging(CONFIG["debug"])
    sessa_lines = load_lines(SESSA_FILE)
    sessb_lines = load_lines(SESSB_FILE)

    if not sessa_lines:
        logging.warning("locales/sessa.txt is empty or missing")
    if not sessb_lines:
        logging.warning("locales/sessb.txt is empty or missing")

    app_a = Client(
        "session_a",
        api_id=CONFIG["api_id"],
        api_hash=CONFIG["api_hash"],
        session_string=CONFIG["session_a_string"],
    )
    app_b = Client(
        "session_b",
        api_id=CONFIG["api_id"],
        api_hash=CONFIG["api_hash"],
        session_string=CONFIG["session_b_string"],
    )

    await app_a.start()
    await app_b.start()
    await ensure_ids()
    register_handlers()

    try:
        await idle()
    finally:
        if conversation_task and not conversation_task.done():
            conversation_task.cancel()
        await app_a.stop()
        await app_b.stop()


if __name__ == "__main__":
    asyncio.run(main())
