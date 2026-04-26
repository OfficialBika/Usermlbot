import asyncio
import html
import json
import logging
import os
import random
import re
import sqlite3
import time
import unicodedata
from datetime import datetime, timedelta
from typing import Any, List, Optional, Set, Tuple
from zoneinfo import ZoneInfo

from dotenv import load_dotenv
from pyrogram import Client, filters, idle
from pyrogram.enums import ChatAction, ChatType, ParseMode
from pyrogram.errors import FloodWait

# Important for PM2 / old environment cache
load_dotenv(override=True)

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
LOCALES_DIR = os.path.join(BASE_DIR, "locales")
SESSA_FILE = os.path.join(LOCALES_DIR, "sessa.txt")
SESSB_FILE = os.path.join(LOCALES_DIR, "sessb.txt")

DATA_DIR = os.getenv("DATA_DIR", BASE_DIR).strip() or BASE_DIR
os.makedirs(DATA_DIR, exist_ok=True)

TZ_NAME = os.getenv("TZ", "Asia/Yangon").strip() or "Asia/Yangon"
LOCAL_TZ = ZoneInfo(TZ_NAME)

BOT_CONFIG_FILE = os.path.join(
    DATA_DIR,
    os.getenv("BOT_CONFIG_FILE", "bot_config.json").strip() or "bot_config.json",
)
DB_FILE = os.path.join(
    DATA_DIR,
    os.getenv("DB_FILE", "catch_history.db").strip() or "catch_history.db",
)

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

DEFAULT_RARITY_CONFIG: dict[str, dict[str, Any]] = {
    "🔵": {"name": "Common", "enabled": False},
    "🟠": {"name": "Rare", "enabled": False},
    "🟣": {"name": "Epic", "enabled": False},
    "🟡": {"name": "Legendary", "enabled": False},
    "💮": {"name": "Mythical", "enabled": False},
    "⚜️": {"name": "Divine", "enabled": False},
    "❓": {"name": "Supreme or Cataphract", "enabled": False},
}

app_a: Optional[Client] = None
app_b: Optional[Client] = None

session_a_id: Optional[int] = None
session_b_id: Optional[int] = None

sessa_lines: List[str] = []
sessb_lines: List[str] = []

CONFIG: dict[str, Any] = {}

# Human chat loop state
enabled_groups: Set[int] = set()
conversation_tasks: dict[int, asyncio.Task] = {}

# Owner mention duplicate protection
alert_seen: dict[Tuple[int, int], float] = {}
alert_seen_lock = asyncio.Lock()
ALERT_DEDUPE_TTL_SECONDS = 180

# Auto-forward / catch system state
SOURCE_GROUPS_CONFIG: dict[int, dict[str, Any]] = {}
RARITY_CONFIG: dict[str, dict[str, Any]] = {}
FORWARD_RARITY: list[str] = []

auto_forward_paused = False
auto_forward_error = False
active_time_seconds = 0.0
last_active_start: Optional[float] = None

pending_responses: dict[Tuple[str, int], dict[str, Any]] = {}
pending_lock = asyncio.Lock()

processed_spawn_messages: set[Tuple[int, int]] = set()
processed_result_messages: set[Tuple[str, int, int]] = set()
processed_lock = asyncio.Lock()

db_conn: Optional[sqlite3.Connection] = None
db_lock = asyncio.Lock()


def now_local() -> datetime:
    return datetime.now(LOCAL_TZ)


def now_local_str(fmt: str = "%Y-%m-%d %H:%M:%S") -> str:
    return now_local().strftime(fmt)


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


def getenv_optional_int(name: str, default: Optional[int] = None) -> Optional[int]:
    value = os.getenv(name)
    if value is None or value.strip() == "":
        return default
    return int(value.strip())


def getenv_float(name: str, default: float) -> float:
    value = os.getenv(name)
    if value is None or value.strip() == "":
        return default
    return float(value.strip())


def clean_session_string(value: str, name: str) -> str:
    if value is None:
        raise RuntimeError(f"Missing required environment variable: {name}")

    s = value.strip()

    if (s.startswith('"') and s.endswith('"')) or (s.startswith("'") and s.endswith("'")):
        s = s[1:-1].strip()

    s = re.sub(r"\s+", "", s)

    if not s:
        raise RuntimeError(f"{name} is empty after cleaning")

    bad_chars = [ch for ch in s if not (ch.isalnum() or ch in "-_=")]
    if bad_chars:
        sample = "".join(bad_chars[:10])
        raise RuntimeError(
            f"{name} contains invalid characters: {sample!r}. "
            f"Please paste a valid Pyrogram session string."
        )

    return s


def getenv_session(name: str) -> str:
    return clean_session_string(getenv_required(name), name)


def parse_int_set(raw: str, env_name: str) -> Set[int]:
    result: Set[int] = set()

    raw = raw.replace("\n", ",")
    parts = raw.split(",")

    for part in parts:
        value = part.strip()
        if not value:
            continue

        try:
            result.add(int(value))
        except ValueError as exc:
            raise RuntimeError(
                f"Invalid integer in {env_name}: {value!r}. "
                f"Use format like: 123456789,987654321"
            ) from exc

    if not result:
        raise RuntimeError(f"{env_name} is empty")

    return result


def getenv_int_set(primary_name: str, fallback_name: str) -> Set[int]:
    raw = os.getenv(primary_name)
    used_name = primary_name

    if raw is None or raw.strip() == "":
        raw = os.getenv(fallback_name)
        used_name = fallback_name

    if raw is None or raw.strip() == "":
        raise RuntimeError(
            f"Missing required environment variable: {primary_name} or {fallback_name}"
        )

    return parse_int_set(raw, used_name)


def parse_session_keys(raw: str, default: str = "a") -> Set[str]:
    raw = (raw or default).strip().lower()
    result = {x.strip() for x in raw.replace(";", ",").split(",") if x.strip()}
    result = {x for x in result if x in {"a", "b"}}
    if not result:
        result = {default}
    return result


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

    group_ids = getenv_int_set("GROUP_IDS", "GROUP_ID")
    log_group_id = getenv_optional_int("LOG_GROUP_ID", default=next(iter(group_ids)))

    auto_forward_enabled = getenv_bool("AUTO_FORWARD_ENABLED", False)
    bot_id = getenv_optional_int("BOT_ID")
    responder_bot_id = getenv_optional_int("RESPONDER_BOT_ID")

    if auto_forward_enabled:
        if bot_id is None:
            raise RuntimeError("BOT_ID is required when AUTO_FORWARD_ENABLED=true")
        if responder_bot_id is None:
            raise RuntimeError("RESPONDER_BOT_ID is required when AUTO_FORWARD_ENABLED=true")

    catch_min_delay = getenv_float("CATCH_MIN_DELAY", 2.0)
    catch_max_delay = getenv_float("CATCH_MAX_DELAY", 3.0)
    if catch_min_delay > catch_max_delay:
        catch_min_delay, catch_max_delay = catch_max_delay, catch_min_delay

    return {
        "api_id": int(getenv_required("API_ID")),
        "api_hash": getenv_required("API_HASH"),
        "session_a_string": getenv_session("SESSION_A_STRING"),
        "session_b_string": getenv_session("SESSION_B_STRING"),
        "owner_ids": getenv_int_set("OWNER_IDS", "OWNER_ID"),
        "group_ids": group_ids,
        "owner_tag": owner_tag,
        "min_reply_delay": min_delay,
        "max_reply_delay": max_delay,
        "reply_chance": reply_chance,
        "loop_pause_delay": getenv_float("LOOP_PAUSE_DELAY", 0.0),
        "debug": getenv_bool("DEBUG", False),
        "auto_forward_enabled": auto_forward_enabled,
        "auto_group_enabled_default": getenv_bool("AUTO_GROUPS_ENABLED_BY_DEFAULT", False),
        "bot_id": bot_id,
        "responder_bot_id": responder_bot_id,
        "log_group_id": log_group_id,
        "auto_catch_sessions": parse_session_keys(os.getenv("AUTO_CATCH_SESSIONS", "a"), "a"),
        "success_name": os.getenv("SUCCESS_NAME", "").strip(),
        "catch_min_delay": catch_min_delay,
        "catch_max_delay": catch_max_delay,
        "auto_delete_catch_command": getenv_bool("AUTO_DELETE_CATCH_COMMAND", True),
        "catch_delete_after_seconds": getenv_float("CATCH_DELETE_AFTER_SECONDS", 1.0),
        "pending_max_age_seconds": getenv_int("PENDING_MAX_AGE_SECONDS", 180),
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


async def send_log(text: str, parse_html: bool = False, app: Optional[Client] = None) -> None:
    client = app or app_a or app_b
    log_group_id = CONFIG.get("log_group_id")

    if client is None or not log_group_id:
        return

    try:
        await client.send_message(
            log_group_id,
            text,
            parse_mode=ParseMode.HTML if parse_html else None,
            disable_web_page_preview=True,
        )
    except FloodWait as e:
        logging.warning("send_log FloodWait: sleeping %s seconds", e.value)
        await asyncio.sleep(e.value)
    except Exception as e:
        logging.warning("send_log failed: %s", e)


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


def init_database() -> None:
    global db_conn

    db_conn = sqlite3.connect(DB_FILE, check_same_thread=False)
    cursor = db_conn.cursor()

    cursor.execute("""
        CREATE TABLE IF NOT EXISTS caught_characters (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            catch_date TEXT,
            character_name TEXT,
            rarity TEXT,
            anime TEXT,
            status TEXT,
            group_id INTEGER
        )
    """)

    cursor.execute("""
        CREATE TABLE IF NOT EXISTS failed_attempts (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            attempt_date TEXT,
            character_name TEXT,
            reason TEXT,
            group_id INTEGER
        )
    """)

    cursor.execute("""
        CREATE TABLE IF NOT EXISTS ignored_characters (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            ignore_date TEXT,
            character_name TEXT,
            rarity TEXT,
            reason TEXT,
            group_id INTEGER
        )
    """)

    db_conn.commit()


async def db_execute(query: str, params: tuple = ()) -> None:
    if db_conn is None:
        return

    async with db_lock:
        cur = db_conn.cursor()
        cur.execute(query, params)
        db_conn.commit()


async def db_fetchall(query: str, params: tuple = ()) -> list[tuple]:
    if db_conn is None:
        return []

    async with db_lock:
        cur = db_conn.cursor()
        cur.execute(query, params)
        return cur.fetchall()


async def db_fetchone(query: str, params: tuple = ()) -> Optional[tuple]:
    if db_conn is None:
        return None

    async with db_lock:
        cur = db_conn.cursor()
        cur.execute(query, params)
        return cur.fetchone()


async def log_caught_character(name: str, rarity: str, anime: str, group_id: int) -> None:
    await db_execute(
        """
        INSERT INTO caught_characters
        (catch_date, character_name, rarity, anime, status, group_id)
        VALUES (?, ?, ?, ?, ?, ?)
        """,
        (now_local_str(), name, rarity, anime, "success", group_id),
    )


async def log_failed_attempt(name: str, reason: str, group_id: int) -> None:
    await db_execute(
        """
        INSERT INTO failed_attempts
        (attempt_date, character_name, reason, group_id)
        VALUES (?, ?, ?, ?)
        """,
        (now_local_str(), name, reason, group_id),
    )


async def log_ignored_character(name: str, rarity: str, reason: str, group_id: int) -> None:
    await db_execute(
        """
        INSERT INTO ignored_characters
        (ignore_date, character_name, rarity, reason, group_id)
        VALUES (?, ?, ?, ?, ?)
        """,
        (now_local_str(), name, rarity, reason, group_id),
    )


async def get_history_by_date(date: str) -> list[tuple]:
    return await db_fetchall(
        """
        SELECT character_name, rarity, anime, catch_date, group_id
        FROM caught_characters
        WHERE DATE(catch_date) = ?
        ORDER BY catch_date DESC
        """,
        (date,),
    )


async def get_failed_by_date(date: str) -> list[tuple]:
    return await db_fetchall(
        """
        SELECT character_name, reason, attempt_date, group_id
        FROM failed_attempts
        WHERE DATE(attempt_date) = ?
        ORDER BY attempt_date DESC
        """,
        (date,),
    )


async def get_ignored_by_date(date: str) -> list[tuple]:
    return await db_fetchall(
        """
        SELECT character_name, rarity, reason, ignore_date, group_id
        FROM ignored_characters
        WHERE DATE(ignore_date) = ?
        ORDER BY ignore_date DESC
        """,
        (date,),
    )


async def get_all_dates() -> list[str]:
    caught = await db_fetchall(
        "SELECT DISTINCT DATE(catch_date) FROM caught_characters ORDER BY DATE(catch_date) DESC"
    )
    failed = await db_fetchall(
        "SELECT DISTINCT DATE(attempt_date) FROM failed_attempts ORDER BY DATE(attempt_date) DESC"
    )
    ignored = await db_fetchall(
        "SELECT DISTINCT DATE(ignore_date) FROM ignored_characters ORDER BY DATE(ignore_date) DESC"
    )

    dates = {x[0] for x in caught + failed + ignored if x and x[0]}
    return sorted(dates, reverse=True)


def init_auto_config() -> None:
    global SOURCE_GROUPS_CONFIG, RARITY_CONFIG, FORWARD_RARITY

    enabled_default = CONFIG.get("auto_group_enabled_default", False)

    SOURCE_GROUPS_CONFIG = {
        gid: {
            "name": f"Group {gid}",
            "enabled": enabled_default,
        }
        for gid in CONFIG["group_ids"]
    }

    RARITY_CONFIG = {
        emoji: dict(data)
        for emoji, data in DEFAULT_RARITY_CONFIG.items()
    }

    saved = load_saved_auto_config()

    if saved:
        for gid_raw, group_data in saved.get("groups", {}).items():
            try:
                gid = int(gid_raw)
            except Exception:
                continue

            if gid not in SOURCE_GROUPS_CONFIG:
                SOURCE_GROUPS_CONFIG[gid] = {
                    "name": str(gid),
                    "enabled": False,
                }

            if isinstance(group_data, dict):
                SOURCE_GROUPS_CONFIG[gid]["name"] = group_data.get(
                    "name",
                    SOURCE_GROUPS_CONFIG[gid]["name"],
                )
                SOURCE_GROUPS_CONFIG[gid]["enabled"] = bool(
                    group_data.get("enabled", SOURCE_GROUPS_CONFIG[gid]["enabled"])
                )

        for emoji, rarity_data in saved.get("rarities", {}).items():
            if emoji not in RARITY_CONFIG:
                RARITY_CONFIG[emoji] = {
                    "name": str(emoji),
                    "enabled": False,
                }

            if isinstance(rarity_data, dict):
                RARITY_CONFIG[emoji]["name"] = rarity_data.get(
                    "name",
                    RARITY_CONFIG[emoji]["name"],
                )
                RARITY_CONFIG[emoji]["enabled"] = bool(
                    rarity_data.get("enabled", RARITY_CONFIG[emoji]["enabled"])
                )

    update_forward_rarity()


def load_saved_auto_config() -> Optional[dict]:
    if not os.path.exists(BOT_CONFIG_FILE):
        return None

    try:
        with open(BOT_CONFIG_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, dict) else None
    except Exception as e:
        logging.warning("Failed to load %s: %s", BOT_CONFIG_FILE, e)
        return None


def save_auto_config() -> None:
    data = {
        "groups": SOURCE_GROUPS_CONFIG,
        "rarities": RARITY_CONFIG,
    }

    with open(BOT_CONFIG_FILE, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=4, ensure_ascii=False)


def update_forward_rarity() -> None:
    global FORWARD_RARITY
    FORWARD_RARITY = [
        emoji
        for emoji, config in RARITY_CONFIG.items()
        if config.get("enabled")
    ]


def get_group_name(chat_id: int) -> str:
    return SOURCE_GROUPS_CONFIG.get(chat_id, {}).get("name", str(chat_id))


def is_group_enabled(chat_id: int) -> bool:
    return bool(SOURCE_GROUPS_CONFIG.get(chat_id, {}).get("enabled", False))


def is_rarity_enabled(emoji: Optional[str]) -> bool:
    if not emoji:
        return True
    return bool(RARITY_CONFIG.get(emoji, {}).get("enabled", False))


def chat_is_known_or_allowed(chat_id: int) -> bool:
    return (
        chat_id in CONFIG.get("group_ids", set())
        or chat_id in SOURCE_GROUPS_CONFIG
        or chat_id == CONFIG.get("log_group_id")
    )


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


def normalize_character_name(value: str) -> str:
    value = re.sub(r"[\[\]🏀🎮]", "", value or "")
    return normalize_text(value)


def is_spawn_alert_message(m) -> bool:
    raw_text = m.text or ""
    raw_caption = m.caption or ""
    raw_content = f"{raw_text}\n{raw_caption}"

    has_trigger_emoji = any(emoji in raw_content for emoji in TRIGGER_EMOJIS)

    normalized = normalize_text(raw_content)
    has_trigger_keyword = any(keyword in normalized for keyword in TRIGGER_KEYWORDS)

    return has_trigger_emoji or has_trigger_keyword


def extract_rarity_from_message(message_text: str) -> Optional[str]:
    for emoji in RARITY_CONFIG.keys():
        if emoji in message_text:
            return emoji
    return None


def extract_character_name_from_message(message_text: str) -> Optional[str]:
    match = re.search(r"/catch\s+\[?(.*?)\]?\s*$", message_text, re.IGNORECASE | re.DOTALL)
    if match:
        value = match.group(1).strip()
        return re.sub(r"[\[\]🏀🎮]", "", value).strip()
    return None


def extract_catch_command(response_text: str) -> Optional[str]:
    patterns = [
        r"Hint\s*[:：]\s*(/catch\s+[^\n]+)",
        r"Full\s*[:：]\s*(/catch\s+[^\n]+)",
        r"(/catch\s+[^\n]+)",
    ]

    for pattern in patterns:
        match = re.search(pattern, response_text or "", re.IGNORECASE)
        if match:
            return " ".join(match.group(1).strip().split())

    return None


def is_success_message(message_text: str) -> bool:
    normalized = normalize_text(message_text)

    success_name = CONFIG.get("success_name", "")
    if success_name:
        expected = normalize_text(
            f"『{success_name}』, ʏᴏᴜ ɢᴏᴛ ᴀ ɴᴇᴡ ᴄʜᴀʀᴀᴄᴛᴇʀ"
        )
        if expected in normalized:
            return True

    return "you got a new character" in normalized


def extract_label_value(text: str, labels: list[str]) -> str:
    normalized = unicodedata.normalize("NFKC", text or "")

    for label in labels:
        pattern = rf"{re.escape(label)}\s*[:：]\s*(.+?)(?:\n|$)"
        match = re.search(pattern, normalized, re.IGNORECASE)
        if match:
            return match.group(1).strip()

    return "Unknown"


def is_character_spawn_text(message_text: str) -> bool:
    normalized = normalize_text(message_text)
    return (
        "a character has spawned" in normalized
        or "add this character" in normalized
        or "/catch" in normalized
    )


def is_attention_text(message_text: str) -> bool:
    normalized = normalize_text(message_text)
    return "attention" in normalized or "captcha" in normalized


def parse_command(text: str) -> str:
    text = (text or "").strip()
    if not text:
        return ""

    first = text.split()[0].strip()
    first = first.split("@")[0]
    return first.lower()


def format_id_list(ids: Set[int]) -> str:
    return ", ".join(str(x) for x in sorted(ids))


def format_seconds(seconds: float) -> str:
    return str(timedelta(seconds=int(seconds)))


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

            msg_a = await send_human(app_a, group_id, None, get_text("a"))

            if group_id not in enabled_groups:
                break

            if not msg_a:
                await asyncio.sleep(2)
                continue

            msg_b = await send_human(app_b, group_id, msg_a.id, get_text("b"))

            if group_id not in enabled_groups:
                break

            if not msg_b:
                await asyncio.sleep(2)
                continue

            await send_human(app_a, group_id, msg_b.id, get_text("a"))

            loop_pause = CONFIG.get("loop_pause_delay", 0.0)
            if loop_pause > 0:
                await asyncio.sleep(loop_pause)

    except asyncio.CancelledError:
        pass

    except Exception as e:
        logging.warning("conversation_loop failed for %s: %s", group_id, e)

    finally:
        conversation_tasks.pop(group_id, None)


async def start_group_loop(group_id: int) -> bool:
    enabled_groups.add(group_id)

    old_task = conversation_tasks.get(group_id)
    if old_task and not old_task.done():
        return False

    conversation_tasks[group_id] = asyncio.create_task(conversation_loop(group_id))
    return True


async def stop_group_loop(group_id: int) -> bool:
    was_enabled = group_id in enabled_groups
    enabled_groups.discard(group_id)

    task = conversation_tasks.pop(group_id, None)
    if task and not task.done():
        task.cancel()

    return was_enabled or bool(task)


async def mark_alert_seen(chat_id: int, message_id: int) -> bool:
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
            return await app.send_message(chat_id, text, reply_to_message_id=reply_to)

        return await app.send_message(chat_id, text)

    except FloodWait as e:
        logging.warning("send_owner_mention FloodWait: sleeping %s seconds", e.value)
        await asyncio.sleep(e.value)
        return None

    except Exception as e:
        logging.warning("send_owner_mention failed: %s", e)
        return None


async def handle_spawn_alert(app: Client, m, source_name: str) -> None:
    try:
        chat_id = getattr(m.chat, "id", None)
        if chat_id is None:
            return

        if not chat_is_known_or_allowed(chat_id):
            return

        is_bot_message = bool((m.from_user and m.from_user.is_bot) or m.sender_chat)
        if not is_bot_message:
            return

        if not is_spawn_alert_message(m):
            return

        first_time = await mark_alert_seen(chat_id, m.id)
        if not first_time:
            return

        await send_owner_mention(app, chat_id, m.id)

    except Exception as e:
        logging.warning("handle_spawn_alert_%s failed: %s", source_name, e)


def start_active_timer() -> None:
    global last_active_start

    if last_active_start is None:
        last_active_start = time.monotonic()


def stop_active_timer() -> None:
    global last_active_start, active_time_seconds

    if last_active_start is not None:
        active_time_seconds += time.monotonic() - last_active_start
        last_active_start = None


def get_total_active_time() -> float:
    total = active_time_seconds
    if last_active_start is not None:
        total += time.monotonic() - last_active_start
    return total


async def mark_spawn_processed(chat_id: int, message_id: int) -> bool:
    key = (chat_id, message_id)

    async with processed_lock:
        if key in processed_spawn_messages:
            return False

        processed_spawn_messages.add(key)

        if len(processed_spawn_messages) > 3000:
            processed_spawn_messages.clear()

        return True


async def mark_result_processed(kind: str, chat_id: int, message_id: int) -> bool:
    key = (kind, chat_id, message_id)

    async with processed_lock:
        if key in processed_result_messages:
            return False

        processed_result_messages.add(key)

        if len(processed_result_messages) > 3000:
            processed_result_messages.clear()

        return True


async def cleanup_stale_pending() -> None:
    max_age = CONFIG.get("pending_max_age_seconds", 180)
    now = now_local()

    async with pending_lock:
        stale_keys = []

        for pending_id, pending in pending_responses.items():
            timestamp = pending.get("timestamp")
            if not timestamp:
                stale_keys.append(pending_id)
                continue

            if (now - timestamp).total_seconds() > max_age:
                stale_keys.append(pending_id)

        for pending_id in stale_keys:
            pending_responses.pop(pending_id, None)


async def select_pending_response(session_key: str, character_name: str):
    await cleanup_stale_pending()

    now = now_local()
    normalized_name = normalize_character_name(character_name)

    async with pending_lock:
        candidates = []

        for pending_id, pending in pending_responses.items():
            if pending.get("session_key") != session_key:
                continue

            if pending.get("waiting_for_result"):
                continue

            timestamp = pending.get("timestamp")
            if not timestamp:
                continue

            if (now - timestamp).total_seconds() > 120:
                continue

            candidates.append((pending_id, pending))

        if not candidates:
            return None, None

        if normalized_name and normalized_name != "unknown":
            matched = [
                (pending_id, pending)
                for pending_id, pending in candidates
                if normalize_character_name(pending.get("character_name", "")) == normalized_name
            ]

            if matched:
                matched.sort(key=lambda item: item[1]["timestamp"], reverse=True)
                return matched[0]

        candidates.sort(key=lambda item: item[1]["timestamp"], reverse=True)
        return candidates[0]


async def add_pending_response(key: Tuple[str, int], pending: dict[str, Any]) -> None:
    async with pending_lock:
        pending_responses[key] = pending


async def update_pending_response(key: Tuple[str, int], updates: dict[str, Any]) -> None:
    async with pending_lock:
        if key in pending_responses:
            pending_responses[key].update(updates)


async def pop_pending_by_group(chat_id: int) -> Optional[dict[str, Any]]:
    async with pending_lock:
        matching = [
            (pending_id, pending)
            for pending_id, pending in pending_responses.items()
            if pending.get("original_chat_id") == chat_id
        ]

        if not matching:
            return None

        matching.sort(
            key=lambda item: (
                not item[1].get("waiting_for_result", False),
                item[1].get("timestamp", now_local()),
            )
        )

        pending_id, pending = matching[0]
        pending_responses.pop(pending_id, None)
        return pending


async def pop_pending_by_reply(chat_id: int, reply_to_message_id: int) -> Optional[dict[str, Any]]:
    async with pending_lock:
        for pending_id, pending in list(pending_responses.items()):
            if pending.get("original_chat_id") != chat_id:
                continue

            if pending.get("my_message_id") != reply_to_message_id:
                continue

            return pending_responses.pop(pending_id, None)

    return None


def get_message_text(m) -> str:
    return m.text or m.caption or ""


async def handle_attention_log(app: Client, m, session_key: str) -> bool:
    message_text = get_message_text(m)
    if not is_attention_text(message_text):
        return False

    group_name = get_group_name(m.chat.id)
    safe_msg = html.escape(message_text[:500])
    safe_group = html.escape(group_name)

    await send_log(
        "🚨 <b>⚠️ ATTENTION REQUIRED ⚠️</b>\n"
        "━━━━━━━━━━━━━━━━━━━━\n"
        f"<b>Session:</b> {html.escape(session_key)}\n"
        f"<b>Group:</b> {safe_group}\n"
        f"<b>Group ID:</b> <code>{m.chat.id}</code>\n"
        f"<b>Message:</b>\n{safe_msg}\n"
        "━━━━━━━━━━━━━━━━━━━━\n"
        f"<b>⏰ Time:</b> {html.escape(now_local_str())}",
        parse_html=True,
        app=app,
    )
    return True


async def handle_auto_forward_spawn(app: Client, session_key: str, m) -> None:
    if not CONFIG.get("auto_forward_enabled"):
        return

    if session_key not in CONFIG.get("auto_catch_sessions", {"a"}):
        return

    if auto_forward_paused or auto_forward_error:
        return

    bot_id = CONFIG.get("bot_id")
    responder_bot_id = CONFIG.get("responder_bot_id")

    if not bot_id or not responder_bot_id:
        return

    if not m.chat or not m.chat.id:
        return

    chat_id = m.chat.id

    if chat_id not in SOURCE_GROUPS_CONFIG:
        return

    if not is_group_enabled(chat_id):
        return

    if not m.from_user or m.from_user.id != bot_id:
        return

    message_text = get_message_text(m)

    if await handle_attention_log(app, m, session_key):
        return

    if not is_character_spawn_text(message_text):
        return

    first_processor = await mark_spawn_processed(chat_id, m.id)
    if not first_processor:
        return

    rarity = extract_rarity_from_message(message_text)
    character_name = extract_character_name_from_message(message_text) or "Unknown"
    group_name = get_group_name(chat_id)

    if rarity and not is_rarity_enabled(rarity):
        await log_ignored_character(
            character_name,
            rarity,
            f"Ignored because {rarity} rarity is disabled",
            chat_id,
        )

        await send_log(
            "⏭️ <b>Character IGNORED</b>\n"
            f"Character: {html.escape(character_name)}\n"
            f"Rarity: {html.escape(rarity)} "
            f"({html.escape(RARITY_CONFIG.get(rarity, {}).get('name', 'Unknown'))})\n"
            "Reason: Rarity is DISABLED\n"
            f"Group: {html.escape(group_name)}\n"
            f"Group ID: <code>{chat_id}</code>\n"
            f"⏰ Time: {html.escape(now_local_str('%H:%M:%S'))}",
            parse_html=True,
            app=app,
        )
        return

    try:
        forwarded = await app.forward_messages(
            chat_id=responder_bot_id,
            from_chat_id=chat_id,
            message_ids=m.id,
        )

        forwarded_msg = forwarded[0] if isinstance(forwarded, list) else forwarded

        pending_key = (session_key, forwarded_msg.id)
        await add_pending_response(
            pending_key,
            {
                "session_key": session_key,
                "forwarded_message_id": forwarded_msg.id,
                "original_message_id": m.id,
                "original_chat_id": chat_id,
                "character_name": character_name,
                "rarity": rarity,
                "timestamp": now_local(),
                "waiting_for_result": False,
            },
        )

        rarity_status = f"{rarity} (ENABLED - FORWARD)" if rarity else "No rarity detected (FORWARD by default)"

        await send_log(
            "📨 <b>Character Spawn Forwarded</b>\n"
            f"Session: <code>{html.escape(session_key)}</code>\n"
            f"Character: {html.escape(character_name)}\n"
            f"Rarity: {html.escape(rarity_status)}\n"
            f"Group: {html.escape(group_name)}\n"
            f"Group ID: <code>{chat_id}</code>\n"
            f"⏰ Time: {html.escape(now_local_str('%H:%M:%S'))}",
            parse_html=True,
            app=app,
        )

    except FloodWait as e:
        logging.warning("Auto-forward FloodWait: sleeping %s seconds", e.value)
        await asyncio.sleep(e.value)

    except Exception as e:
        logging.warning("Auto-forward failed: %s", e)
        await send_log(
            f"❌ Auto-forward error: <code>{html.escape(str(e))}</code>",
            parse_html=True,
            app=app,
        )


async def handle_responder_dm(app: Client, session_key: str, m) -> None:
    if not CONFIG.get("auto_forward_enabled"):
        return

    if auto_forward_paused or auto_forward_error:
        return

    responder_bot_id = CONFIG.get("responder_bot_id")
    if not responder_bot_id:
        return

    if m.chat.type != ChatType.PRIVATE:
        return

    if not m.from_user or m.from_user.id != responder_bot_id:
        return

    response_text = get_message_text(m)
    if not response_text:
        return

    normalized_response = unicodedata.normalize("NFKC", response_text)
    name_match = re.search(r"(?:NAME|Name|Nᴀᴍᴇ|ɴᴀᴍᴇ)\s*[:：]\s*([^\n]+)", normalized_response, re.IGNORECASE)
    character_name = name_match.group(1).strip() if name_match else "Unknown"
    character_name = re.sub(r"[\[\]🏀🎮]", "", character_name).strip() or "Unknown"

    catch_command = extract_catch_command(response_text)
    if not catch_command:
        return

    pending_key, pending = await select_pending_response(session_key, character_name)
    if not pending_key or not pending:
        return

    try:
        await asyncio.sleep(random.uniform(CONFIG["catch_min_delay"], CONFIG["catch_max_delay"]))

        sent_message = await app.send_message(pending["original_chat_id"], catch_command)

        await update_pending_response(
            pending_key,
            {
                "character_name": character_name or pending.get("character_name", "Unknown"),
                "catch_command": catch_command,
                "waiting_for_result": True,
                "my_message_id": sent_message.id,
            },
        )

        await send_log(
            "🎣 <b>Catch command sent</b>\n"
            f"Session: <code>{html.escape(session_key)}</code>\n"
            f"Character: {html.escape(character_name)}\n"
            f"Rarity: {html.escape(str(pending.get('rarity') or 'Unknown'))}\n"
            f"Command: <code>{html.escape(catch_command)}</code>\n"
            f"Message ID: <code>{sent_message.id}</code>\n"
            f"⏰ Time: {html.escape(now_local_str('%H:%M:%S'))}",
            parse_html=True,
            app=app,
        )

        if CONFIG.get("auto_delete_catch_command", True):
            asyncio.create_task(
                delete_later(
                    app,
                    pending["original_chat_id"],
                    sent_message.id,
                    CONFIG.get("catch_delete_after_seconds", 1.0),
                )
            )

    except FloodWait as e:
        logging.warning("Catch send FloodWait: sleeping %s seconds", e.value)
        await asyncio.sleep(e.value)

    except Exception as e:
        logging.warning("handle_responder_dm failed: %s", e)
        await send_log(
            f"❌ Catch command send error: <code>{html.escape(str(e))}</code>",
            parse_html=True,
            app=app,
        )


async def delete_later(app: Client, chat_id: int, message_id: int, delay: float) -> None:
    await asyncio.sleep(max(0.0, delay))

    try:
        await app.delete_messages(chat_id, message_id)
    except Exception as e:
        logging.debug("Failed to delete catch command: %s", e)


async def handle_success_edited(app: Client, session_key: str, m) -> None:
    if not CONFIG.get("auto_forward_enabled"):
        return

    if auto_forward_paused or auto_forward_error:
        return

    bot_id = CONFIG.get("bot_id")
    if not bot_id:
        return

    if not m.chat or not m.chat.id:
        return

    chat_id = m.chat.id

    if chat_id not in SOURCE_GROUPS_CONFIG or not is_group_enabled(chat_id):
        return

    if not m.from_user or m.from_user.id != bot_id:
        return

    message_text = get_message_text(m)
    if not is_success_message(message_text):
        return

    first_processor = await mark_result_processed("success", chat_id, m.id)
    if not first_processor:
        return

    normalized = unicodedata.normalize("NFKC", message_text)

    caught_name = extract_label_value(normalized, ["Name", "NAME", "Nᴀᴍᴇ"])
    rarity = extract_label_value(normalized, ["RARITY", "Rarity", "𝙍𝘼𝙍𝙄𝙏𝙔"])
    anime = extract_label_value(normalized, ["Anime", "ANIME", "Aɴɪᴍᴇ"])

    await log_caught_character(caught_name, rarity, anime, chat_id)
    await pop_pending_by_group(chat_id)

    group_name = get_group_name(chat_id)

    await send_log(
        "✅ <b>SUCCESS! Character Caught</b>\n"
        "━━━━━━━━━━━━━━━━━━━━\n"
        f"🫧 Name: {html.escape(caught_name)}\n"
        f"🟣 Rarity: {html.escape(rarity)}\n"
        f"🏖️ Anime: {html.escape(anime)}\n"
        "━━━━━━━━━━━━━━━━━━━━\n"
        f"📍 Group: {html.escape(group_name)}\n"
        f"Group ID: <code>{chat_id}</code>\n"
        f"⏰ Time: {html.escape(now_local_str())}",
        parse_html=True,
        app=app,
    )


async def handle_fail_new_message(app: Client, session_key: str, m) -> None:
    if not CONFIG.get("auto_forward_enabled"):
        return

    if auto_forward_paused or auto_forward_error:
        return

    if not m.chat or not m.chat.id:
        return

    chat_id = m.chat.id

    if chat_id not in SOURCE_GROUPS_CONFIG or not is_group_enabled(chat_id):
        return

    bot_id = CONFIG.get("bot_id")
    if bot_id and (not m.from_user or m.from_user.id != bot_id):
        return

    reply_to_id = getattr(m, "reply_to_message_id", None)
    if reply_to_id is None and getattr(m, "reply_to_message", None):
        reply_to_id = m.reply_to_message.id

    if not reply_to_id:
        return

    message_text = get_message_text(m)
    normalized = normalize_text(message_text)

    reason = None
    if "character already caught" in normalized:
        reason = "Already caught by someone else"
    elif "oops you missed it" in normalized or "you missed it" in normalized:
        reason = "Missed / Too slow"

    if not reason:
        return

    first_processor = await mark_result_processed("fail", chat_id, m.id)
    if not first_processor:
        return

    pending = await pop_pending_by_reply(chat_id, reply_to_id)
    if not pending:
        return

    char_name = pending.get("character_name", "Unknown")
    await log_failed_attempt(char_name, reason, chat_id)

    label = "⚠️ ALREADY CAUGHT" if "Already" in reason else "❌ MISSED"

    await send_log(
        f"{html.escape(label)}\n"
        f"Character: {html.escape(char_name)}\n"
        f"Reason: {html.escape(reason)}\n"
        f"Group: <code>{chat_id}</code>\n"
        f"⏰ Time: {html.escape(now_local_str())}",
        parse_html=True,
        app=app,
    )


def is_owner_message(m) -> bool:
    if not m.from_user:
        return False
    return m.from_user.id in CONFIG["owner_ids"]


def is_command_context(m) -> bool:
    if not m.chat:
        return False

    if m.chat.type == ChatType.PRIVATE and m.from_user and m.from_user.id in CONFIG["owner_ids"]:
        return True

    return chat_is_known_or_allowed(m.chat.id)


async def send_stats(m) -> None:
    await cleanup_stale_pending()

    db_total = (await db_fetchone("SELECT COUNT(*) FROM caught_characters") or (0,))[0]
    db_failed = (await db_fetchone("SELECT COUNT(*) FROM failed_attempts") or (0,))[0]
    db_ignored = (await db_fetchone("SELECT COUNT(*) FROM ignored_characters") or (0,))[0]

    enabled_source_groups = sum(1 for g in SOURCE_GROUPS_CONFIG.values() if g.get("enabled"))
    enabled_rarities = sum(1 for r in RARITY_CONFIG.values() if r.get("enabled"))

    async with pending_lock:
        pending_count = len(pending_responses)

    running_chat_loops = [
        gid for gid, task in conversation_tasks.items()
        if task and not task.done()
    ]

    msg = (
        "<blockquote><b>📊 Current Bot Status</b></blockquote>\n"
        f"🕐 Time: {html.escape(now_local_str())} ({html.escape(TZ_NAME)})\n"
        f"Auto Forward: {'✅ ON' if CONFIG.get('auto_forward_enabled') else '❌ OFF'}\n"
        f"Paused: {'✅ Yes' if auto_forward_paused else '❌ No'}\n"
        f"Error: {'✅ Yes' if auto_forward_error else '❌ No'}\n"
        f"Active Time: {html.escape(format_seconds(get_total_active_time()))}\n"
        f"Total Caught: {db_total}\n"
        f"Total Failed: {db_failed}\n"
        f"Total Ignored: {db_ignored}\n"
        f"Pending Responses: {pending_count}\n"
        f"Enabled Source Groups: {enabled_source_groups}/{len(SOURCE_GROUPS_CONFIG)}\n"
        f"Enabled Rarities: {enabled_rarities}/{len(RARITY_CONFIG)}\n"
        f"Chat Loops Running: {len(running_chat_loops)}\n"
        f"Auto Catch Sessions: {html.escape(','.join(sorted(CONFIG.get('auto_catch_sessions', []))))}"
    )

    await m.reply(msg, parse_mode=ParseMode.HTML)


async def send_help(m) -> None:
    text = (
        "<blockquote><b>📋 Commands</b></blockquote>\n"
        "━━━━━━━━━━━━━━━━━━━━\n"
        "<b>Human Chat Loop:</b>\n"
        "• <code>/open</code> - current group ON\n"
        "• <code>/close</code> - current group OFF\n"
        "• <code>/status</code> - current group status\n"
        "• <code>/statusall</code> - all groups status\n\n"
        "<b>Auto-Forward Control:</b>\n"
        "• <code>yat</code> or <code>pause</code> - pause auto-forward\n"
        "• <code>sa</code> or <code>resume</code> - resume auto-forward\n"
        "• <code>stats</code> or <code>/stats</code> - status\n\n"
        "<b>Group Management:</b>\n"
        "• <code>groups</code> or <code>glist</code> - list groups\n"
        "• <code>gadd [id] [name]</code> - add group\n"
        "• <code>gdel [id]</code> - delete group\n"
        "• <code>gedit [id] [new_name]</code> - edit group name\n"
        "• <code>group on [id]</code> - enable monitoring\n"
        "• <code>group off [id]</code> - disable monitoring\n\n"
        "<b>Rarity Management:</b>\n"
        "• <code>rarity</code> or <code>rlist</code> - list rarities\n"
        "• <code>radd [emoji] [name]</code> - add rarity\n"
        "• <code>rdel [emoji]</code> - delete rarity\n"
        "• <code>redit [emoji] [new_name]</code> - edit rarity name\n"
        "• <code>rarity on [emoji]</code> - forward rarity\n"
        "• <code>rarity off [emoji]</code> - ignore rarity\n\n"
        "<b>History / Test:</b>\n"
        "• <code>history</code> - list dates\n"
        "• <code>YYYY-MM-DD</code> - show date history\n"
        "• <code>test [message]</code> - test rarity detection"
    )
    await m.reply(text, parse_mode=ParseMode.HTML)


async def show_groups(m) -> None:
    if not SOURCE_GROUPS_CONFIG:
        await m.reply("❌ No groups configured.")
        return

    lines = [f"<blockquote><b>📋 Monitored Groups ({len(SOURCE_GROUPS_CONFIG)})</b></blockquote>"]

    for gid, config in SOURCE_GROUPS_CONFIG.items():
        status = "✅ ACTIVE" if config.get("enabled") else "❌ DISABLED"
        lines.append(
            f"• {html.escape(str(config.get('name', gid)))}\n"
            f"  └─ ID: <code>{gid}</code>\n"
            f"  └─ Status: {status}"
        )

    lines.append(
        "\n💡 <b>Commands:</b>\n"
        "• <code>gadd [id] [name]</code>\n"
        "• <code>gdel [id]</code>\n"
        "• <code>gedit [id] [new_name]</code>\n"
        "• <code>group on/off [id]</code>"
    )

    await m.reply("\n".join(lines), parse_mode=ParseMode.HTML)


async def show_rarities(m) -> None:
    forward_items = []
    ignore_items = []

    for emoji, config in RARITY_CONFIG.items():
        action = "FORWARD" if config.get("enabled") else "IGNORE"
        status = "✅ ENABLED" if config.get("enabled") else "❌ DISABLED"
        item = f"  {html.escape(emoji)} → {html.escape(config.get('name', 'Unknown'))} [{action}] {status}"

        if config.get("enabled"):
            forward_items.append(item)
        else:
            ignore_items.append(item)

    lines = [
        "🔮 <b>Rarity Configuration</b>",
        "━━━━━━━━━━━━━━━━━━━━",
        f"\n✨ <b>FORWARD Rarities ({len(forward_items)})</b>",
        *(forward_items or ["  (None)"]),
        f"\n⏭️ <b>IGNORE Rarities ({len(ignore_items)})</b>",
        *(ignore_items or ["  (None)"]),
        "\n💡 <b>Commands:</b>",
        "• <code>radd [emoji] [name]</code>",
        "• <code>rdel [emoji]</code>",
        "• <code>redit [emoji] [new_name]</code>",
        "• <code>rarity on/off [emoji]</code>",
    ]

    await m.reply("\n".join(lines), parse_mode=ParseMode.HTML)


async def show_history_dates(m) -> None:
    dates = await get_all_dates()

    if not dates:
        await m.reply("❌ No history found. Database is empty.")
        return

    lines = ["📅 <b>Available History Dates</b>\n"]

    for date in dates[:20]:
        catches = len(await get_history_by_date(date))
        fails = len(await get_failed_by_date(date))
        ignored = len(await get_ignored_by_date(date))
        lines.append(f"• <code>{html.escape(date)}</code> - ✅ {catches}, ❌ {fails}, ⏭️ {ignored}")

    lines.append("\n💬 <b>Send a date (YYYY-MM-DD) to view details</b>")
    await m.reply("\n".join(lines), parse_mode=ParseMode.HTML)


async def send_history_by_date(m, date: str) -> None:
    catches = await get_history_by_date(date)
    fails = await get_failed_by_date(date)
    ignored = await get_ignored_by_date(date)

    if not catches and not fails and not ignored:
        await m.reply(f"❌ No history found for date: {date}")
        return

    lines = [f"📆 <b>History for {html.escape(date)}</b>\n"]

    if catches:
        lines.append("✅ <b>Successful Catches:</b>")
        for name, rarity, anime, catch_time, group_id in catches:
            lines.append(f"• <b>{html.escape(str(name))}</b> [{html.escape(str(rarity))}] from {html.escape(str(anime))}")

    if fails:
        lines.append("\n❌ <b>Failed Attempts:</b>")
        for name, reason, attempt_time, group_id in fails:
            lines.append(f"• <b>{html.escape(str(name or 'Unknown'))}</b> - {html.escape(str(reason))}")

    if ignored:
        lines.append("\n⏭️ <b>Ignored Characters:</b>")
        for name, rarity, reason, ignore_time, group_id in ignored:
            lines.append(f"• <b>{html.escape(str(name or 'Unknown'))}</b> [{html.escape(str(rarity))}] - {html.escape(str(reason))}")

    await m.reply("\n".join(lines), parse_mode=ParseMode.HTML)


async def test_message_analysis(m) -> None:
    raw = m.text or ""
    test_message = raw.split(maxsplit=1)[1].strip() if len(raw.split(maxsplit=1)) > 1 else ""

    if not test_message:
        await m.reply(
            "❌ Please provide a test message.\n\n"
            "Example:\n"
            "<code>test 🟡 ᴀ ᴄʜᴀʀᴀᴄᴛᴇʀ ʜᴀs sᴘᴀᴡɴᴇᴅ /catch name</code>",
            parse_mode=ParseMode.HTML,
        )
        return

    rarity = extract_rarity_from_message(test_message)
    character_name = extract_character_name_from_message(test_message)

    lines = [
        "🧪 <b>TEST ANALYSIS</b>",
        "━━━━━━━━━━━━━━━━━━━━",
        f"📝 <b>Message:</b>\n{html.escape(test_message[:300])}",
        "",
    ]

    if is_attention_text(test_message):
        lines.append("🚨 <b>Attention/captcha alert would be logged.</b>")

    if rarity:
        enabled = is_rarity_enabled(rarity)
        name = RARITY_CONFIG.get(rarity, {}).get("name", "Unknown")
        lines.append(f"✨ <b>Rarity:</b> {html.escape(rarity)} ({html.escape(name)})")
        lines.append(f"🎯 <b>Action:</b> {'✅ FORWARD' if enabled else '❌ IGNORE'}")
    else:
        lines.append("❓ <b>Rarity:</b> None")
        lines.append("🎯 <b>Action:</b> ✅ FORWARD by default")

    lines.append(f"👤 <b>Character:</b> {html.escape(character_name or 'Unknown')}")
    await m.reply("\n".join(lines), parse_mode=ParseMode.HTML)


async def handle_owner_command(_, m) -> None:
    global auto_forward_paused, auto_forward_error

    try:
        if not is_owner_message(m):
            return

        if not is_command_context(m):
            return

        text = (m.text or "").strip()
        text_lower = text.lower()
        cmd = parse_command(text)
        chat_id = m.chat.id

        if cmd == "/open":
            if chat_id not in CONFIG["group_ids"] and chat_id not in SOURCE_GROUPS_CONFIG:
                await m.reply("❌ This group is not allowed. Add it with gadd first.")
                return

            started = await start_group_loop(chat_id)
            await m.reply(("✅ ON\n" if started else "✅ Already ON\n") + f"group_id={chat_id}")
            return

        if cmd == "/close":
            stopped = await stop_group_loop(chat_id)
            await m.reply(("❌ OFF\n" if stopped else "❌ Already OFF\n") + f"group_id={chat_id}")
            return

        if cmd == "/status":
            running = bool(conversation_tasks.get(chat_id) and not conversation_tasks[chat_id].done())

            status_lines = [
                f"group_id={chat_id}",
                f"enabled={chat_id in enabled_groups}",
                f"loop_running={running}",
                f"owners={format_id_list(CONFIG['owner_ids'])}",
                f"allowed_groups={format_id_list(CONFIG['group_ids'])}",
                f"auto_forward={'ON' if CONFIG.get('auto_forward_enabled') else 'OFF'}",
                f"auto_paused={auto_forward_paused}",
            ]

            await m.reply("\n".join(status_lines))
            return

        if cmd == "/statusall":
            lines = ["📊 All group status", f"owners={format_id_list(CONFIG['owner_ids'])}", ""]

            all_gids = sorted(set(CONFIG["group_ids"]) | set(SOURCE_GROUPS_CONFIG.keys()))
            for gid in all_gids:
                running = bool(conversation_tasks.get(gid) and not conversation_tasks[gid].done())
                lines.append(f"{gid}: chat_loop_enabled={gid in enabled_groups}, running={running}, auto_group_enabled={is_group_enabled(gid)}")

            await m.reply("\n".join(lines))
            return

        if cmd in {"/help", "help"}:
            await send_help(m)
            return

        if text_lower in {"yat", "pause"}:
            auto_forward_paused = True
            auto_forward_error = False
            stop_active_timer()
            await m.reply("⏸️ Auto-forward is now paused.")
            return

        if text_lower in {"sa", "resume"}:
            auto_forward_paused = False
            auto_forward_error = False
            start_active_timer()
            await m.reply("▶️ Auto-forward is now active.")
            return

        if cmd in {"stats", "/stats"}:
            await send_stats(m)
            return

        if text_lower.startswith("gadd"):
            parts = text.split(maxsplit=2)
            if len(parts) < 3:
                await m.reply("❌ Usage: <code>gadd [group_id] [group_name]</code>", parse_mode=ParseMode.HTML)
                return

            try:
                gid = int(parts[1])
            except ValueError:
                await m.reply("❌ Invalid group ID.")
                return

            if gid in SOURCE_GROUPS_CONFIG:
                await m.reply(f"❌ Group ID <code>{gid}</code> already exists.", parse_mode=ParseMode.HTML)
                return

            SOURCE_GROUPS_CONFIG[gid] = {"name": parts[2], "enabled": False}
            save_auto_config()
            await m.reply(
                f"✅ Group added!\nID: <code>{gid}</code>\nName: {html.escape(parts[2])}\nStatus: DISABLED",
                parse_mode=ParseMode.HTML,
            )
            return

        if text_lower.startswith("gdel"):
            parts = text.split()
            if len(parts) < 2:
                await m.reply("❌ Usage: <code>gdel [group_id]</code>", parse_mode=ParseMode.HTML)
                return

            try:
                gid = int(parts[1])
            except ValueError:
                await m.reply("❌ Invalid group ID.")
                return

            if gid not in SOURCE_GROUPS_CONFIG:
                await m.reply(f"❌ Group ID <code>{gid}</code> not found.", parse_mode=ParseMode.HTML)
                return

            old_name = SOURCE_GROUPS_CONFIG[gid].get("name", str(gid))
            del SOURCE_GROUPS_CONFIG[gid]
            save_auto_config()
            await m.reply(f"✅ Group deleted!\nID: <code>{gid}</code>\nName: {html.escape(old_name)}", parse_mode=ParseMode.HTML)
            return

        if text_lower.startswith("gedit"):
            parts = text.split(maxsplit=2)
            if len(parts) < 3:
                await m.reply("❌ Usage: <code>gedit [group_id] [new_name]</code>", parse_mode=ParseMode.HTML)
                return

            try:
                gid = int(parts[1])
            except ValueError:
                await m.reply("❌ Invalid group ID.")
                return

            if gid not in SOURCE_GROUPS_CONFIG:
                await m.reply(f"❌ Group ID <code>{gid}</code> not found.", parse_mode=ParseMode.HTML)
                return

            old_name = SOURCE_GROUPS_CONFIG[gid].get("name", str(gid))
            SOURCE_GROUPS_CONFIG[gid]["name"] = parts[2]
            save_auto_config()
            await m.reply(f"✅ Group name updated!\nID: <code>{gid}</code>\nOld: {html.escape(old_name)}\nNew: {html.escape(parts[2])}", parse_mode=ParseMode.HTML)
            return

        if text_lower in {"groups", "glist", "group list"}:
            await show_groups(m)
            return

        if text_lower.startswith("group on") or text_lower.startswith("group off"):
            parts = text.split()
            if len(parts) < 3:
                await m.reply("❌ Usage: <code>group on/off [group_id]</code>", parse_mode=ParseMode.HTML)
                return

            action = parts[1].lower()
            try:
                gid = int(parts[2])
            except ValueError:
                await m.reply("❌ Invalid group ID.")
                return

            if gid not in SOURCE_GROUPS_CONFIG:
                await m.reply(f"❌ Group ID <code>{gid}</code> not found. Use gadd first.", parse_mode=ParseMode.HTML)
                return

            SOURCE_GROUPS_CONFIG[gid]["enabled"] = action == "on"
            save_auto_config()
            await m.reply(f"{'✅' if action == 'on' else '❌'} Group <code>{gid}</code> is now {'ENABLED' if action == 'on' else 'DISABLED'}", parse_mode=ParseMode.HTML)
            return

        if text_lower.startswith("radd"):
            parts = text.split(maxsplit=2)
            if len(parts) < 3:
                await m.reply("❌ Usage: <code>radd [emoji] [name]</code>", parse_mode=ParseMode.HTML)
                return

            emoji, name = parts[1], parts[2]
            if emoji in RARITY_CONFIG:
                await m.reply(f"❌ Rarity {html.escape(emoji)} already exists.", parse_mode=ParseMode.HTML)
                return

            RARITY_CONFIG[emoji] = {"name": name, "enabled": False}
            update_forward_rarity()
            save_auto_config()
            await m.reply(f"✅ Rarity added!\nEmoji: {html.escape(emoji)}\nName: {html.escape(name)}\nStatus: DISABLED", parse_mode=ParseMode.HTML)
            return

        if text_lower.startswith("rdel"):
            parts = text.split()
            if len(parts) < 2:
                await m.reply("❌ Usage: <code>rdel [emoji]</code>", parse_mode=ParseMode.HTML)
                return

            emoji = parts[1]
            if emoji not in RARITY_CONFIG:
                await m.reply(f"❌ Rarity {html.escape(emoji)} not found.", parse_mode=ParseMode.HTML)
                return

            old_name = RARITY_CONFIG[emoji].get("name", emoji)
            del RARITY_CONFIG[emoji]
            update_forward_rarity()
            save_auto_config()
            await m.reply(f"✅ Rarity deleted!\nEmoji: {html.escape(emoji)}\nName: {html.escape(old_name)}", parse_mode=ParseMode.HTML)
            return

        if text_lower.startswith("redit"):
            parts = text.split(maxsplit=2)
            if len(parts) < 3:
                await m.reply("❌ Usage: <code>redit [emoji] [new_name]</code>", parse_mode=ParseMode.HTML)
                return

            emoji, new_name = parts[1], parts[2]
            if emoji not in RARITY_CONFIG:
                await m.reply(f"❌ Rarity {html.escape(emoji)} not found.", parse_mode=ParseMode.HTML)
                return

            old_name = RARITY_CONFIG[emoji].get("name", emoji)
            RARITY_CONFIG[emoji]["name"] = new_name
            save_auto_config()
            await m.reply(f"✅ Rarity name updated!\nEmoji: {html.escape(emoji)}\nOld: {html.escape(old_name)}\nNew: {html.escape(new_name)}", parse_mode=ParseMode.HTML)
            return

        if text_lower in {"rarity", "rlist", "rarity list", "rarities"}:
            await show_rarities(m)
            return

        if text_lower.startswith("rarity on") or text_lower.startswith("rarity off"):
            parts = text.split()
            if len(parts) < 3:
                await m.reply("❌ Usage: <code>rarity on/off [emoji]</code>", parse_mode=ParseMode.HTML)
                return

            action = parts[1].lower()
            emoji = parts[2]

            if emoji not in RARITY_CONFIG:
                await m.reply(f"❌ Unknown rarity: {html.escape(emoji)}", parse_mode=ParseMode.HTML)
                return

            RARITY_CONFIG[emoji]["enabled"] = action == "on"
            update_forward_rarity()
            save_auto_config()

            action_text = "FORWARD" if RARITY_CONFIG[emoji]["enabled"] else "IGNORE"
            await m.reply(f"{'✅' if action == 'on' else '❌'} Rarity {html.escape(emoji)} ({html.escape(RARITY_CONFIG[emoji].get('name', 'Unknown'))}) is now {action_text}", parse_mode=ParseMode.HTML)
            return

        if text_lower == "history":
            await show_history_dates(m)
            return

        if re.match(r"^\d{4}-\d{2}-\d{2}$", text_lower):
            await send_history_by_date(m, text_lower)
            return

        if text_lower.startswith("test"):
            await test_message_analysis(m)
            return

    except Exception as e:
        logging.warning("owner command handler failed: %s", e)


async def handle_general_message(app: Client, session_key: str, m) -> None:
    try:
        await handle_spawn_alert(app, m, session_key)
        await handle_responder_dm(app, session_key, m)
        await handle_auto_forward_spawn(app, session_key, m)
        await handle_fail_new_message(app, session_key, m)
    except Exception as e:
        logging.warning("handle_general_message_%s failed: %s", session_key, e)


async def handle_edited_message(app: Client, session_key: str, m) -> None:
    try:
        await handle_success_edited(app, session_key, m)
    except Exception as e:
        logging.warning("handle_edited_message_%s failed: %s", session_key, e)


def register_handlers() -> None:
    @app_a.on_message(filters.text)
    async def commands_a(_, m):
        await handle_owner_command(_, m)

    @app_a.on_message()
    async def general_a(_, m):
        await handle_general_message(app_a, "a", m)

    @app_b.on_message()
    async def general_b(_, m):
        await handle_general_message(app_b, "b", m)

    @app_a.on_edited_message()
    async def edited_a(_, m):
        await handle_edited_message(app_a, "a", m)

    @app_b.on_edited_message()
    async def edited_b(_, m):
        await handle_edited_message(app_b, "b", m)


async def shutdown_clients() -> None:
    for gid in list(enabled_groups):
        enabled_groups.discard(gid)

    tasks = [task for task in conversation_tasks.values() if task and not task.done()]

    conversation_tasks.clear()

    for task in tasks:
        task.cancel()

    if tasks:
        await asyncio.gather(*tasks, return_exceptions=True)

    if app_a is not None:
        await app_a.stop()

    if app_b is not None:
        await app_b.stop()

    if db_conn is not None:
        db_conn.close()


async def send_startup_summary() -> None:
    enabled_source_groups = [gid for gid, config in SOURCE_GROUPS_CONFIG.items() if config.get("enabled")]
    enabled_rarities = [emoji for emoji, config in RARITY_CONFIG.items() if config.get("enabled")]

    groups_lines = []
    for gid, config in SOURCE_GROUPS_CONFIG.items():
        groups_lines.append(
            f"• {html.escape(str(config.get('name', gid)))}\n"
            f"  └─ ID: <code>{gid}</code>\n"
            f"  └─ Status: {'✅ ACTIVE' if config.get('enabled') else '❌ DISABLED'}"
        )

    await send_log(
        "🚀 <b>Secmlbot Started</b>\n"
        "━━━━━━━━━━━━━━━━━━━━\n"
        f"Session A: <code>{session_a_id}</code>\n"
        f"Session B: <code>{session_b_id}</code>\n"
        f"Auto Forward: {'✅ ON' if CONFIG.get('auto_forward_enabled') else '❌ OFF'}\n"
        f"Auto Catch Sessions: <code>{html.escape(','.join(sorted(CONFIG.get('auto_catch_sessions', []))))}</code>\n"
        f"Total Source Groups: {len(SOURCE_GROUPS_CONFIG)} | Active: {len(enabled_source_groups)}\n"
        f"Total Rarities: {len(RARITY_CONFIG)} | Forward: {len(enabled_rarities)}\n"
        f"Timezone: <code>{html.escape(TZ_NAME)}</code>\n"
        f"Database: <code>{html.escape(os.path.basename(DB_FILE))}</code>\n"
        "━━━━━━━━━━━━━━━━━━━━\n"
        f"📋 <b>Groups:</b>\n{chr(10).join(groups_lines) if groups_lines else '(None)'}\n\n"
        f"✨ <b>Forward Rarities:</b> {html.escape(', '.join(enabled_rarities) if enabled_rarities else '(None)')}\n"
        f"⏭️ <b>Ignore Rarities:</b> {html.escape(', '.join([e for e, c in RARITY_CONFIG.items() if not c.get('enabled')]) or '(None)')}\n\n"
        "💡 Commands: <code>/help</code> or <code>help</code>",
        parse_html=True,
        app=app_a,
    )


async def main() -> None:
    global CONFIG, app_a, app_b, sessa_lines, sessb_lines

    CONFIG = load_config()
    setup_logging(CONFIG["debug"])

    init_database()
    init_auto_config()

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
        in_memory=True,
    )

    app_b = Client(
        "session_b",
        api_id=CONFIG["api_id"],
        api_hash=CONFIG["api_hash"],
        session_string=CONFIG["session_b_string"],
        in_memory=True,
    )

    await app_a.start()
    await app_b.start()

    await ensure_ids()
    register_handlers()

    start_active_timer()

    logging.warning(
        "Started successfully | session_a_id=%s | session_b_id=%s | groups=%s | auto_forward=%s",
        session_a_id,
        session_b_id,
        format_id_list(CONFIG["group_ids"]),
        CONFIG.get("auto_forward_enabled"),
    )

    await send_startup_summary()

    try:
        await idle()
    finally:
        stop_active_timer()
        await shutdown_clients()


if __name__ == "__main__":
    asyncio.run(main())
