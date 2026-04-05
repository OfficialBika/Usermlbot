import asyncio
import json
import logging
import os
import random
from logging.handlers import RotatingFileHandler
from typing import Dict, List, Optional, Set

from pyrogram import Client, filters, idle
from pyrogram.enums import ChatType
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

logger = logging.getLogger("mlbb-auto-chat")

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

    formatter = logging.Formatter("%(asctime)s | %(levelname)s | %(name)s | %(message)s")

    file_handler = RotatingFileHandler(LOG_FILE, maxBytes=2_000_000, backupCount=5, encoding="utf-8")
    file_handler.setFormatter(formatter)

    stream_handler = logging.StreamHandler()
    stream_handler.setFormatter(formatter)

    root.handlers.clear()
    root.addHandler(file_handler)
    root.addHandler(stream_handler)


def ensure_project_files() -> None:
    os.makedirs(os.path.join(BASE_DIR, "data"), exist_ok=True)
    os.makedirs(LOG_DIR, exist_ok=True)
    os.makedirs(LOCALES_DIR, exist_ok=True)

    if not os.path.exists(STATE_FILE):
        save_state(DEFAULT_STATE.copy())

    if not os.path.exists(SESSA_FILE):
        with open(SESSA_FILE, "w", encoding="utf-8") as f:
            f.write("ဟုတ်တယ်ဗျ\nအဲဒီ angle ကောင်းတယ်\nposition ယူပြီးမှ fight ဝင်ပါ\n")

    if not os.path.exists(SESSB_FILE):
        with open(SESSB_FILE, "w", encoding="utf-8") as f:
            f.write("objective control က အရေးကြီးပါတယ်\nlane priority ယူပြီးမှ turtle သွားပါ\n")


def load_config() -> Dict[str, object]:
    if not os.path.exists(CONFIG_FILE):
        raise FileNotFoundError(
            "config.json မတွေ့ပါ။ config.json.example ကို copy လုပ်ပြီး config.json အဖြစ် rename ပြုလုပ်ပါ။"
        )

    cfg = read_json(CONFIG_FILE)

    required = [
        "api_id", "api_hash", "session_a", "session_b",
        "owner_id", "group_id", "enable_two_way",
        "min_reply_delay", "max_reply_delay"
    ]
    missing = [k for k in required if k not in cfg]
    if missing:
        raise ValueError(f"config.json ထဲမှာ မရှိတဲ့ keys: {', '.join(missing)}")

    if not isinstance(cfg["api_id"], int):
        raise ValueError("api_id must be integer")
    if not isinstance(cfg["owner_id"], int):
        raise ValueError("owner_id must be integer")
    if not isinstance(cfg["group_id"], int):
        raise ValueError("group_id must be integer")
    if float(cfg["min_reply_delay"]) < 8:
        raise ValueError("min_reply_delay must be at least 8 seconds for safer usage")
    if float(cfg["max_reply_delay"]) < float(cfg["min_reply_delay"]):
        raise ValueError("max_reply_delay must be greater than or equal to min_reply_delay")

    return cfg


def load_state() -> Dict[str, object]:
    try:
        data = read_json(STATE_FILE)
        return {
            "enabled": bool(data.get("enabled", False)),
            "sessa_index": int(data.get("sessa_index", 0)),
            "sessb_index": int(data.get("sessb_index", 0)),
            "sessa_history": list(data.get("sessa_history", [])),
            "sessb_history": list(data.get("sessb_history", [])),
        }
    except FileNotFoundError:
        return DEFAULT_STATE.copy()
    except Exception as e:
        logger.exception("Failed to load state: %s", e)
        return DEFAULT_STATE.copy()


def save_state(data: Dict[str, object]) -> None:
    with open(STATE_FILE, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)


def load_lines(path: str) -> List[str]:
    lines: List[str] = []
    try:
        with open(path, "r", encoding="utf-8") as f:
            for raw in f:
                line = raw.strip()
                if not line or line.startswith("#"):
                    continue
                lines.append(line)
    except FileNotFoundError:
        logger.warning("Locale file not found: %s", path)
    except Exception as e:
        logger.exception("Failed to load locale file %s: %s", path, e)
    return lines


def reload_locales() -> None:
    global sessa_lines, sessb_lines
    sessa_lines = load_lines(SESSA_FILE)
    sessb_lines = load_lines(SESSB_FILE)
    logger.info("Locales loaded | sessa=%d | sessb=%d", len(sessa_lines), len(sessb_lines))


def normalize_text(text: str) -> str:
    return (text or "").strip().lower()


def is_text_message(message: Message) -> bool:
    return bool(message.text and message.text.strip())


def allowed_chat(message: Message) -> bool:
    if message.chat is None:
        return False
    if message.chat.id != CONFIG["group_id"]:
        return False
    return message.chat.type in {ChatType.GROUP, ChatType.SUPERGROUP}


def is_control_command(message: Message) -> bool:
    return normalize_text(message.text) in {"/open", "/close", "/status", "/reload", "/help"}


async def ensure_me_ids() -> None:
    global session_a_id, session_b_id
    if session_a_id is None:
        me = await app_a.get_me()
        session_a_id = me.id
    if session_b_id is None:
        me = await app_b.get_me()
        session_b_id = me.id


def get_next_line(which: str):
    if which == "sessa":
        lines = sessa_lines
        key = "sessa_index"
        history_key = "sessa_history"
    else:
        lines = sessb_lines
        key = "sessb_index"
        history_key = "sessb_history"

    if not lines:
        return None

    idx = int(state.get(key, 0))
    history: Set[str] = set(state.get(history_key, []))

    for _ in range(len(lines)):
        if idx >= len(lines):
            idx = 0
        line = lines[idx]
        normalized = normalize_text(line)
        idx = (idx + 1) % len(lines)
        if normalized and normalized not in history:
            history.add(normalized)
            state[key] = idx
            state[history_key] = list(history)[-10000:]
            save_state(state)
            return line

    # all unique lines already used once; reset the cycle cleanly
    logger.info("All %s lines were used once. Resetting %s history.", which, which)
    state[history_key] = []
    state[key] = idx
    save_state(state)
    return get_next_line(which)


def set_enabled(value: bool) -> None:
    state["enabled"] = value
    save_state(state)


async def safe_send_reply(sender_app: Client, chat_id: int, reply_to_message_id: int, text: str):
    try:
        delay = random.uniform(float(CONFIG["min_reply_delay"]), float(CONFIG["max_reply_delay"]))
        await asyncio.sleep(delay)

        msg = await sender_app.send_message(
            chat_id=chat_id,
            text=text,
            reply_to_message_id=reply_to_message_id
        )
        recent_auto_messages.add(msg.id)
        if len(recent_auto_messages) > 5000:
            recent_auto_messages.clear()
        logger.info("Sent reply | chat_id=%s | reply_to=%s | msg_id=%s", chat_id, reply_to_message_id, msg.id)
        return msg

    except FloodWait as e:
        logger.warning("FloodWait: %s seconds", e.value)
        await asyncio.sleep(e.value)
        try:
            msg = await sender_app.send_message(
                chat_id=chat_id,
                text=text,
                reply_to_message_id=reply_to_message_id
            )
            recent_auto_messages.add(msg.id)
            return msg
        except Exception as e2:
            logger.exception("Retry after FloodWait failed: %s", e2)
            return None
    except RPCError as e:
        logger.exception("Telegram RPCError: %s", e)
        return None
    except Exception as e:
        logger.exception("Unexpected send error: %s", e)
        return None


async def reply_status(message: Message) -> None:
    text = (
        f"Status: {'ON' if state['enabled'] else 'OFF'}\n"
        f"Two-way: {'ON' if CONFIG['enable_two_way'] else 'OFF'}\n"
        f"sessa.txt lines: {len(sessa_lines)}\n"
        f"sessb.txt lines: {len(sessb_lines)}\n"
        f"sessa next index: {state.get('sessa_index', 0)}\n"
        f"sessb next index: {state.get('sessb_index', 0)}\n"
        f"group_id: {CONFIG['group_id']}"
    )
    await message.reply_text(text)


def register_handlers() -> None:
    @app_a.on_message(filters.text)
    async def owner_commands(_, message: Message):
        if not allowed_chat(message):
            return
        if not message.from_user:
            return
        if message.from_user.id != CONFIG["owner_id"]:
            return

        cmd = normalize_text(message.text)

        if cmd == "/open":
            set_enabled(True)
            logger.info("Bot enabled by owner")
            await message.reply_text("Auto reply is now ON.")
        elif cmd == "/close":
            set_enabled(False)
            logger.info("Bot disabled by owner")
            await message.reply_text("Auto reply is now OFF.")
        elif cmd == "/status":
            await reply_status(message)
        elif cmd == "/reload":
            reload_locales()
            await message.reply_text(
                f"Locales reloaded.\n"
                f"sessa.txt: {len(sessa_lines)} lines\n"
                f"sessb.txt: {len(sessb_lines)} lines"
            )
        elif cmd == "/help":
            await message.reply_text(
                "/open - start auto reply\n"
                "/close - stop auto reply\n"
                "/status - show current status\n"
                "/reload - reload locales files\n"
                "/help - show commands"
            )

    @app_a.on_message(filters.text)
    async def watch_a(_, message: Message):
        if not allowed_chat(message) or not state["enabled"] or not message.from_user:
            return
        if not is_text_message(message) or is_control_command(message):
            return

        await ensure_me_ids()

        if message.id in recent_auto_messages:
            return

        async with message_lock:
            user_id = message.from_user.id

            if user_id == session_a_id:
                if last_trigger["from_a"] == message.id:
                    return
                last_trigger["from_a"] = message.id

                reply_text = get_next_line("sessb")
                if not reply_text:
                    logger.warning("sessb.txt has no usable lines")
                    return

                await safe_send_reply(app_b, int(CONFIG["group_id"]), message.id, reply_text)
                return


    @app_b.on_message(filters.text)
    async def watch_b(_, message: Message):
        if not CONFIG["enable_two_way"]:
            return
        if not allowed_chat(message) or not state["enabled"] or not message.from_user:
            return
        if not is_text_message(message) or is_control_command(message):
            return

        await ensure_me_ids()

        if message.id in recent_auto_messages:
            return

        async with message_lock:
            user_id = message.from_user.id
            if user_id == session_b_id:
                if last_trigger["from_b"] == message.id:
                    return
                last_trigger["from_b"] = message.id

                reply_text = get_next_line("sessa")
                if not reply_text:
                    return

                await safe_send_reply(app_a, int(CONFIG["group_id"]), message.id, reply_text)


async def startup() -> None:
    global CONFIG, app_a, app_b, state

    ensure_project_files()
    CONFIG = load_config()
    setup_logging(bool(CONFIG.get("debug", False)))

    state = load_state()
    reload_locales()

    app_a = Client(str(CONFIG["session_a"]), api_id=int(CONFIG["api_id"]), api_hash=str(CONFIG["api_hash"]))
    app_b = Client(str(CONFIG["session_b"]), api_id=int(CONFIG["api_id"]), api_hash=str(CONFIG["api_hash"]))
    register_handlers()

    await app_a.start()
    await app_b.start()
    await ensure_me_ids()

    me_a = await app_a.get_me()
    me_b = await app_b.get_me()

    logger.info("Session A logged in as %s (%s)", me_a.first_name, me_a.id)
    logger.info("Session B logged in as %s (%s)", me_b.first_name, me_b.id)
    logger.info("Bot started | enabled=%s | two_way=%s | group_id=%s",
                state["enabled"], CONFIG["enable_two_way"], CONFIG["group_id"])

    print(f"Session A: {me_a.first_name} ({me_a.id})")
    print(f"Session B: {me_b.first_name} ({me_b.id})")
    print(f"Enabled : {state['enabled']}")
    print(f"Two-way : {CONFIG['enable_two_way']}")
    print(f"Group ID: {CONFIG['group_id']}")
    print("Commands: /open /close /status /reload /help")


async def shutdown() -> None:
    logger.info("Shutting down...")
    if app_a is not None:
        try:
            await app_a.stop()
        except Exception as e:
            logger.exception("Error stopping app_a: %s", e)
    if app_b is not None:
        try:
            await app_b.stop()
        except Exception as e:
            logger.exception("Error stopping app_b: %s", e)


async def main() -> None:
    try:
        await startup()
        await idle()
    finally:
        await shutdown()


if __name__ == "__main__":
    asyncio.run(main())
