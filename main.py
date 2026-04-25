import asyncio
import logging
import os
import random
import time
import unicodedata
from typing import List, Optional, Set, Tuple

from dotenv import load_dotenv
from pyrogram import Client, filters, idle
from pyrogram.enums import ChatAction
from pyrogram.errors import FloodWait

load_dotenv()

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
LOCALES_DIR = os.path.join(BASE_DIR, "locales")
SESSA_FILE = os.path.join(LOCALES_DIR, "sessa.txt")
SESSB_FILE = os.path.join(LOCALES_DIR, "sessb.txt")

DEFAULT_OWNER_TAG = "@Official_Bika"

EMOJIS = ["🙂", "😄", "😉", "😎", "🔥", "✨", "😂", "🥰"]

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

session_a_id: Optional[int] = None
session_b_id: Optional[int] = None

sessa_lines: List[str] = []
sessb_lines: List[str] = []

CONFIG = {}

# Multi-group state
enabled_groups: Set[int] = set()
conversation_tasks: dict[int, asyncio.Task] = {}

# Spawn alert duplicate protection
alert_seen: dict[Tuple[int, int], float] = {}
alert_seen_lock = asyncio.Lock()
ALERT_DEDUPE_TTL_SECONDS = 180


def getenv_required(name: str) -> str:
    value = os.getenv(name)
    if value is None or value.strip() == "":
        raise RuntimeError(f"Missing required environment variable: {name}")
    return value.strip()


def getenv_bool(name: str, default: bool = False) -> bool:
    value = os.getenv(name)
    if value is None or value.strip() == "":
        return default
    return value.strip().lower() in {"1", "true", "yes", "y", "on"}


def getenv_int(name: str, default: int) -> int:
    value = os.getenv(name)
    if value is None or value.strip() == "":
        return default
    return int(value.strip())


def getenv_float(name: str, default: float) -> float:
    value = os.getenv(name)
    if value is None or value.strip() == "":
        return default
    return float(value.strip())


def parse_int_set(raw: str, env_name: str) -> Set[int]:
    result: Set[int] = set()

    # Allow comma/newline separated values
    raw = raw.replace("\n", ",")
    parts = raw.split(",")

    for part in parts:
        value = part.strip()
        if not value:
            continue

        try:
            result.add(int(value))
        except ValueError:
            raise RuntimeError(
                f"Invalid integer in {env_name}: {value!r}. "
                f"Use format like: 123456789,987654321"
            )

    if not result:
        raise RuntimeError(f"{env_name} is empty")

    return result


def getenv_int_set(primary_name: str, fallback_name: str) -> Set[int]:
    """
    Prefer OWNER_IDS / GROUP_IDS.
    Fallback to old OWNER_ID / GROUP_ID for backward compatibility.
    """
    raw = os.getenv(primary_name)
    used_name = primary_name

    if raw is None or raw.strip() == "":
        raw = os.getenv(fallback_name)
        used_name = fallback_name

    if raw is None or raw.strip() == "":
        raise RuntimeError(
            f"Missing required environment variable: {primary_name} "
            f"or {fallback_name}"
        )

    return parse_int_set(raw, used_name)


def load_config() -> dict:
    min_delay = getenv_int("MIN_REPLY_DELAY", 2)
    max_delay = getenv_int("MAX_REPLY_DELAY", 4)

    if min_delay > max_delay:
        min_delay, max_delay = max_delay, min_delay

    reply_chance = getenv_float("REPLY_CHANCE", 0.25)
    reply_chance = max(0.0, min(1.0, reply_chance))

    owner_tag = os.getenv("OWNER_TAG", DEFAULT_OWNER_TAG).strip()
    if not owner_tag:
        owner_tag = DEFAULT_OWNER_TAG

    return {
        "api_id": int(getenv_required("API_ID")),
        "api_hash": getenv_required("API_HASH"),
        "session_a_string": getenv_required("SESSION_A_STRING"),
        "session_b_string": getenv_required("SESSION_B_STRING"),

        # New multi value envs
        "owner_ids": getenv_int_set("OWNER_IDS", "OWNER_ID"),
        "group_ids": getenv_int_set("GROUP_IDS", "GROUP_ID"),

        "owner_tag": owner_tag,
        "min_reply_delay": min_delay,
        "max_reply_delay": max_delay,
        "reply_chance": reply_chance,
        "loop_pause_delay": getenv_float("LOOP_PAUSE_DELAY", 0.0),
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

    if app_a is None or app_b is None:
        raise RuntimeError("Clients are not initialized")

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


async def mark_alert_seen(chat_id: int, message_id: int) -> bool:
    """
    Return True only for first detector.
    This prevents app_a and app_b from mentioning owner twice for same alert.
    """
    now = time.monotonic()
    key = (chat_id, message_id)

    async with alert_seen_lock:
        expired_keys = [
            old_key
            for old_key, seen_at in alert_seen.items()
            if now - seen_at > ALERT_DEDUPE_TTL_SECONDS
        ]

        for old_key in expired_keys:
            alert_seen.pop(old_key, None)

        if key in alert_seen:
            return False

        alert_seen[key] = now
        return True


async def send_owner_mention(
    app: Client,
    chat_id: int,
    reply_to: Optional[int] = None,
):
    text = CONFIG.get("owner_tag", DEFAULT_OWNER_TAG)

    try:
        if reply_to:
            return await app.send_message(
                chat_id,
                text,
                reply_to_message_id=reply_to,
            )

        return await app.send_message(chat_id, text)

    except FloodWait as e:
        logging.warning("send_owner_mention FloodWait: sleeping %s seconds", e.value)
        await asyncio.sleep(e.value)
        return None

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
        await asyncio.sleep(
            random.uniform(
                CONFIG["min_reply_delay"],
                CONFIG["max_reply_delay"],
            )
        )

        await app.send_chat_action(chat_id, ChatAction.TYPING)
        await asyncio.sleep(random.uniform(0.3, 0.8))

        use_reply = bool(reply_to) and (
            force_reply or random.random() < CONFIG["reply_chance"]
        )

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


async def conversation_loop(group_id: int):
    try:
        while group_id in enabled_groups:
            if app_a is None or app_b is None:
                await asyncio.sleep(2)
                continue

            msg_a = await send_human(
                app_a,
                group_id,
                None,
                get_text("a"),
            )

            if group_id not in enabled_groups:
                break

            if not msg_a:
                await asyncio.sleep(2)
                continue

            msg_b = await send_human(
                app_b,
                group_id,
                msg_a.id,
                get_text("b"),
            )

            if group_id not in enabled_groups:
                break

            if not msg_b:
                await asyncio.sleep(2)
                continue

            await send_human(
                app_a,
                group_id,
                msg_b.id,
                get_text("a"),
            )

            loop_pause = CONFIG.get("loop_pause_delay", 0.0)
            if loop_pause > 0:
                await asyncio.sleep(loop_pause)

    except asyncio.CancelledError:
        pass

    except Exception as e:
        logging.warning("conversation_loop failed for %s: %s", group_id, e)

    finally:
        conversation_tasks.pop(group_id, None)


def is_owner_message(m) -> bool:
    if not m.from_user:
        return False
    return m.from_user.id in CONFIG["owner_ids"]


def parse_command(text: str) -> str:
    text = (text or "").strip()
    if not text:
        return ""

    first = text.split()[0].strip()
    first = first.split("@")[0]
    return first.lower()


def format_id_list(ids: Set[int]) -> str:
    return ", ".join(str(x) for x in sorted(ids))


async def start_group_loop(group_id: int) -> bool:
    """
    Return True if newly started.
    Return False if already running.
    """
    enabled_groups.add(group_id)

    old_task = conversation_tasks.get(group_id)
    if old_task and not old_task.done():
        return False

    conversation_tasks[group_id] = asyncio.create_task(conversation_loop(group_id))
    return True


async def stop_group_loop(group_id: int) -> bool:
    """
    Return True if stopped.
    Return False if it was already off.
    """
    was_enabled = group_id in enabled_groups
    enabled_groups.discard(group_id)

    task = conversation_tasks.pop(group_id, None)
    if task and not task.done():
        task.cancel()

    return was_enabled or bool(task)


async def handle_spawn_alert(app: Client, m, source_name: str) -> None:
    try:
        is_bot_message = bool(
            (m.from_user and m.from_user.is_bot)
            or m.sender_chat
        )

        if not is_bot_message:
            return

        if not is_spawn_alert_message(m):
            return

        first_time = await mark_alert_seen(m.chat.id, m.id)
        if not first_time:
            return

        await send_owner_mention(app, m.chat.id, m.id)

    except Exception as e:
        logging.warning("handle_spawn_alert_%s failed: %s", source_name, e)


def register_handlers() -> None:
    group_chats = list(CONFIG["group_ids"])

    @app_a.on_message(filters.chat(group_chats) & filters.text)
    async def commands(_, m):
        try:
            if not is_owner_message(m):
                return

            cmd = parse_command(m.text)
            chat_id = m.chat.id

            if cmd == "/open":
                started = await start_group_loop(chat_id)

                if started:
                    await m.reply(
                        "✅ ON\n"
                        f"group_id={chat_id}"
                    )
                else:
                    await m.reply(
                        "✅ Already ON\n"
                        f"group_id={chat_id}"
                    )

            elif cmd == "/close":
                stopped = await stop_group_loop(chat_id)

                if stopped:
                    await m.reply(
                        "❌ OFF\n"
                        f"group_id={chat_id}"
                    )
                else:
                    await m.reply(
                        "❌ Already OFF\n"
                        f"group_id={chat_id}"
                    )

            elif cmd == "/status":
                running = bool(
                    conversation_tasks.get(chat_id)
                    and not conversation_tasks[chat_id].done()
                )

                status_lines = [
                    f"group_id={chat_id}",
                    f"enabled={chat_id in enabled_groups}",
                    f"loop_running={running}",
                    f"owners={format_id_list(CONFIG['owner_ids'])}",
                    f"allowed_groups={format_id_list(CONFIG['group_ids'])}",
                ]

                await m.reply("\n".join(status_lines))

            elif cmd == "/statusall":
                lines = [
                    "📊 All group status",
                    f"owners={format_id_list(CONFIG['owner_ids'])}",
                    "",
                ]

                for gid in sorted(CONFIG["group_ids"]):
                    running = bool(
                        conversation_tasks.get(gid)
                        and not conversation_tasks[gid].done()
                    )

                    lines.append(
                        f"{gid}: "
                        f"enabled={gid in enabled_groups}, "
                        f"running={running}"
                    )

                await m.reply("\n".join(lines))

            elif cmd == "/help":
                await m.reply(
                    "/open - current group ON\n"
                    "/close - current group OFF\n"
                    "/status - current group status\n"
                    "/statusall - all groups status\n"
                    "/help"
                )

        except Exception as e:
            logging.warning("commands handler failed: %s", e)

    @app_a.on_message(filters.chat(group_chats))
    async def detect_spawn_alert_a(_, m):
        await handle_spawn_alert(app_a, m, "a")

    @app_b.on_message(filters.chat(group_chats))
    async def detect_spawn_alert_b(_, m):
        await handle_spawn_alert(app_b, m, "b")


async def shutdown_clients() -> None:
    for gid in list(enabled_groups):
        await stop_group_loop(gid)

    tasks = [
        task
        for task in conversation_tasks.values()
        if task and not task.done()
    ]

    for task in tasks:
        task.cancel()

    if tasks:
        await asyncio.gather(*tasks, return_exceptions=True)

    if app_a is not None:
        await app_a.stop()

    if app_b is not None:
        await app_b.stop()


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
        await shutdown_clients()


if __name__ == "__main__":
    asyncio.run(main())
