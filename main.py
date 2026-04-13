import asyncio
import logging
import os
import random
from typing import List, Optional

from dotenv import load_dotenv
from aiohttp import web
from pyrogram import Client, filters, idle
from pyrogram.enums import ChatAction
from pyrogram.errors import FloodWait

load_dotenv()

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
LOCALES_DIR = os.path.join(BASE_DIR, "locales")
SESSA_FILE = os.path.join(LOCALES_DIR, "sessa.txt")
SESSB_FILE = os.path.join(LOCALES_DIR, "sessb.txt")

EMOJIS = ["🙂", "😄", "😉", "😎", "🔥", "✨", "😂", "🥰"]

app_a: Optional[Client] = None
app_b: Optional[Client] = None
session_a_id = None
session_b_id = None
sessa_lines: List[str] = []
sessb_lines: List[str] = []
enabled = False
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
        "enable_two_way": getenv_bool("ENABLE_TWO_WAY", False),
        "min_reply_delay": min_delay,
        "max_reply_delay": max_delay,
        "debug": getenv_bool("DEBUG", False),
        "port": getenv_int("PORT", 10000),
        "host": os.getenv("HOST", "0.0.0.0"),
    }


def setup_logging(debug: bool) -> None:
    level = logging.DEBUG if debug else logging.INFO
    logging.basicConfig(level=level, format="%(asctime)s | %(levelname)s | %(message)s")


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


async def send_human(app: Client, chat_id: int, reply_to: Optional[int], text: str):
    try:
        await asyncio.sleep(random.uniform(CONFIG["min_reply_delay"], CONFIG["max_reply_delay"]))
        await app.send_chat_action(chat_id, ChatAction.TYPING)
        await asyncio.sleep(random.uniform(2, 4))

        if random.random() < 0.8 or not reply_to:
            msg = await app.send_message(chat_id, text)
        else:
            msg = await app.send_message(chat_id, text, reply_to_message_id=reply_to)
        return msg
    except FloodWait as e:
        logging.warning("FloodWait: sleeping %s seconds", e.value)
        await asyncio.sleep(e.value)
        return None
    except Exception as e:
        logging.exception("send_human error: %s", e)
        return None


async def health(_: web.Request) -> web.Response:
    status = {
        "ok": True,
        "enabled": enabled,
        "session_a_started": app_a is not None,
        "session_b_started": app_b is not None,
    }
    return web.json_response(status, status=200)


async def root(_: web.Request) -> web.Response:
    return web.Response(text="Usermlbot is running", status=200)


async def start_http_server() -> web.AppRunner:
    web_app = web.Application()
    web_app.router.add_get("/", root)
    web_app.router.add_get("/health", health)

    runner = web.AppRunner(web_app)
    await runner.setup()
    site = web.TCPSite(runner, host=CONFIG["host"], port=CONFIG["port"])
    await site.start()

    logging.info("HTTP server started on %s:%s", CONFIG["host"], CONFIG["port"])
    return runner


def register_handlers() -> None:
    @app_a.on_message(filters.chat(CONFIG["group_id"]) & filters.text)
    async def commands(_, m):
        global enabled
        if not m.from_user:
            return
        if m.from_user.id != CONFIG["owner_id"]:
            return

        if m.text == "/open":
            enabled = True
            await m.reply("✅ ON")
            first_text = get_text("a")
            await send_human(app_a, CONFIG["group_id"], None, first_text)
        elif m.text == "/close":
            enabled = False
            await m.reply("❌ OFF")
        elif m.text == "/status":
            await m.reply(
                f"enabled={enabled}\n"
                f"group_id={CONFIG['group_id']}\n"
                f"enable_two_way={CONFIG['enable_two_way']}"
            )
        elif m.text == "/help":
            await m.reply("/open\n/close\n/status\n/help")

    @app_b.on_message(filters.chat(CONFIG["group_id"]) & filters.incoming & filters.text)
    async def watch_b(_, m):
        if not enabled:
            return
        if not m.from_user:
            return

        await ensure_ids()
        logging.debug("watch_b triggered: from=%s text=%s", m.from_user.id, m.text)

        if m.from_user.id == session_a_id:
            logging.info("A sent -> B reply")
            msg_b = await send_human(app_b, CONFIG["group_id"], m.id, get_text("b"))
            if msg_b:
                logging.info("B sent -> A reply")
                await send_human(app_a, CONFIG["group_id"], msg_b.id, get_text("a"))

    if CONFIG["enable_two_way"]:
        @app_a.on_message(filters.chat(CONFIG["group_id"]) & filters.incoming & filters.text)
        async def watch_a(_, m):
            if not enabled:
                return
            if not m.from_user:
                return

            await ensure_ids()
            logging.debug("watch_a triggered: from=%s text=%s", m.from_user.id, m.text)

            if m.from_user.id == session_b_id:
                logging.info("B sent -> A reply (two-way)")
                msg_a = await send_human(app_a, CONFIG["group_id"], m.id, get_text("a"))
                if msg_a:
                    logging.info("A sent -> B reply (two-way)")
                    await send_human(app_b, CONFIG["group_id"], msg_a.id, get_text("b"))


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

    logging.info("Session A ID: %s", session_a_id)
    logging.info("Session B ID: %s", session_b_id)

    register_handlers()
    http_runner = await start_http_server()

    logging.info("Bot running...")
    try:
        await idle()
    finally:
        logging.info("Shutting down...")
        await http_runner.cleanup()
        await app_a.stop()
        await app_b.stop()


if __name__ == "__main__":
    asyncio.run(main())
