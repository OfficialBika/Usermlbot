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
from io import BytesIO
from typing import Any, List, Optional, Set, Tuple
from zoneinfo import ZoneInfo

from dotenv import load_dotenv
from pyrogram import Client, filters, idle
from pyrogram.enums import ChatAction, ChatType, ParseMode
from pyrogram.errors import FloodWait

try:
    import cv2
    import numpy as np
except Exception:
    cv2 = None
    np = None

try:
    from motor.motor_asyncio import AsyncIOMotorClient
except Exception:
    AsyncIOMotorClient = None

try:
    from PIL import Image
    import imagehash
except Exception:
    Image = None
    imagehash = None

import hashlib

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

DEFAULT_OWNER_TAG = "@HODAKAMORISHI"

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

# Responder DM duplicate protection
responder_dm_seen: set[Tuple[str, int, int]] = set()
responder_dm_lock = asyncio.Lock()

db_conn: Optional[sqlite3.Connection] = None
db_lock = asyncio.Lock()

# Captcha auto-solver state
pending_captchas: dict[int, dict[str, Any]] = {}
captcha_message_to_request: dict[Tuple[str, int, int], int] = {}
captcha_lock = asyncio.Lock()
processed_captcha_messages: set[Tuple[str, int, int]] = set()
captcha_recent_items: dict[Tuple[str, int, int], dict[str, Any]] = {}
_LEARNED_DIGIT_TEMPLATE_CACHE: Optional[dict[str, list[Any]]] = None
easyocr_reader = None

# Direct MongoDB catch system
direct_mongo_client = None
direct_items_collection = None

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
    min_delay = getenv_float("MIN_REPLY_DELAY", 2.0)
    max_delay = getenv_float("MAX_REPLY_DELAY", 4.0)

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
    direct_db_catch_enabled = getenv_bool("DIRECT_DB_CATCH_ENABLED", False)
    bot_id = getenv_optional_int("BOT_ID")

    # Forward target bot. Keep RESPONDER_BOT_ID as default target.
    # RESPONDER_BOT_IDS is optional and only used for accepting replies from multiple resolver bots.
    responder_bot_id = getenv_optional_int("RESPONDER_BOT_ID")
    responder_bot_ids: Set[int] = set()
    raw_responder_ids = os.getenv("RESPONDER_BOT_IDS", "").strip()
    if raw_responder_ids:
        responder_bot_ids = parse_int_set(raw_responder_ids, "RESPONDER_BOT_IDS")
    elif responder_bot_id is not None:
        responder_bot_ids = {responder_bot_id}

    if auto_forward_enabled:
        if bot_id is None:
            raise RuntimeError("BOT_ID is required when AUTO_FORWARD_ENABLED=true")
        if not direct_db_catch_enabled and responder_bot_id is None and not responder_bot_ids:
            raise RuntimeError("RESPONDER_BOT_ID or RESPONDER_BOT_IDS is required when AUTO_FORWARD_ENABLED=true, unless DIRECT_DB_CATCH_ENABLED=true")

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
        "source_bot_strict": getenv_bool("SOURCE_BOT_STRICT", getenv_bool("BOT_ID_STRICT", True)),
        "responder_bot_id": responder_bot_id or (next(iter(responder_bot_ids)) if responder_bot_ids else None),
        "responder_bot_ids": responder_bot_ids,
        "debug_responder": getenv_bool("DEBUG_RESPONDER", True),
        "log_group_id": log_group_id,
        "auto_catch_sessions": parse_session_keys(os.getenv("AUTO_CATCH_SESSIONS", "a,b"), "a"),
        "success_name": os.getenv("SUCCESS_NAME", "").strip(),
        "catch_min_delay": catch_min_delay,
        "catch_max_delay": catch_max_delay,
        "auto_delete_catch_command": getenv_bool("AUTO_DELETE_CATCH_COMMAND", True),
        "catch_delete_after_seconds": getenv_float("CATCH_DELETE_AFTER_SECONDS", 1.0),
        "pending_max_age_seconds": getenv_int("PENDING_MAX_AGE_SECONDS", 180),

        # Captcha auto-solver (for your own private captcha flow)
        "captcha_solver_enabled": getenv_bool("CAPTCHA_SOLVER_ENABLED", False),
        "captcha_bot_id": getenv_optional_int("CAPTCHA_BOT_ID", default=bot_id),
        "captcha_target_groups": getenv_int_set("CAPTCHA_TARGET_GROUPS", "GROUP_IDS") if (os.getenv("CAPTCHA_TARGET_GROUPS") or "").strip() else group_ids,
        "captcha_solver_sessions": parse_session_keys(os.getenv("CAPTCHA_SOLVER_SESSIONS", os.getenv("AUTO_CATCH_SESSIONS", "a,b")), "a"),
        "captcha_auto_approve": getenv_bool("CAPTCHA_AUTO_APPROVE", False),
        "captcha_auto_approve_methods": {
            x.strip()
            for x in os.getenv("CAPTCHA_AUTO_APPROVE_METHODS", "plain_image_marker,learned_template_match,tesseract_ocr,easyocr_ocr,ocr_vote").split(",")
            if x.strip()
        },
        "captcha_min_confidence": getenv_float("MIN_SOLVER_CONFIDENCE", getenv_float("CAPTCHA_MIN_CONFIDENCE", 0.60)),
        "captcha_auto_min_confidence": getenv_float("CAPTCHA_AUTO_APPROVE_MIN_CONFIDENCE", 0.75),
        "captcha_approval_timeout": getenv_int("APPROVAL_TIMEOUT_SEC", 120),
        "enable_ocr_fallback": getenv_bool("ENABLE_OCR_FALLBACK", True),
        "enable_tesseract_ocr": getenv_bool("ENABLE_TESSERACT_OCR", True),
        "enable_easyocr": getenv_bool("ENABLE_EASYOCR", False),
        "captcha_log_no_answer": getenv_bool("CAPTCHA_LOG_NO_ANSWER", True),
        "captcha_debug_save": getenv_bool("CAPTCHA_DEBUG_SAVE", False),
        "captcha_allow_coordinate_click": getenv_bool("CAPTCHA_ALLOW_COORDINATE_CLICK", False),
        "captcha_learning_enabled": getenv_bool("CAPTCHA_LEARNING_ENABLED", True),
        "captcha_learning_min_templates": getenv_int("CAPTCHA_LEARNING_MIN_TEMPLATES", 3),
        "captcha_learn_template_limit_per_digit": getenv_int("CAPTCHA_LEARN_TEMPLATE_LIMIT_PER_DIGIT", 200),

        # Direct MongoDB catch lookup. This bypasses responder bot reply parsing.
        "direct_db_catch_enabled": direct_db_catch_enabled,
        "direct_db_mongo_uri": os.getenv("DIRECT_DB_MONGO_URI", os.getenv("MONGO_URI", "")).strip(),
        "direct_db_name": os.getenv("DIRECT_DB_NAME", os.getenv("DB_NAME", "")).strip(),
        "direct_db_collection": os.getenv("DIRECT_DB_COLLECTION", os.getenv("MEDIA_COLLECTION", "items")).strip() or "items",
        "direct_db_sessions": parse_session_keys(os.getenv("DIRECT_DB_CATCH_SESSIONS", os.getenv("AUTO_CATCH_SESSIONS", "a,b")), "a"),
        "direct_db_command_name": os.getenv("DIRECT_DB_COMMAND_NAME", "/catch").strip() or "/catch",
        "direct_db_source_bot_key": os.getenv("DIRECT_DB_SOURCE_BOT_KEY", "catcher").strip() or "catcher",
        "direct_db_use_file_unique_id": getenv_bool("DIRECT_DB_USE_FILE_UNIQUE_ID", True),
        "direct_db_use_sha256": getenv_bool("DIRECT_DB_USE_SHA256", True),
        "direct_db_use_phash": getenv_bool("DIRECT_DB_USE_PHASH", False),
        "direct_db_phash_threshold": getenv_int("DIRECT_DB_PHASH_THRESHOLD", 8),
        "direct_db_phash_scan_limit": getenv_int("DIRECT_DB_PHASH_SCAN_LIMIT", 5000),
        "direct_db_name_mode": os.getenv("DIRECT_DB_CATCH_NAME_MODE", "hint").strip().lower() or "hint",
        "direct_db_command_field": os.getenv("DIRECT_DB_CATCH_COMMAND_FIELD", "command").strip() or "command",
        "direct_db_hint_field": os.getenv("DIRECT_DB_CATCH_HINT_FIELD", "hint").strip() or "hint",
        "direct_db_name_field": os.getenv("DIRECT_DB_CATCH_NAME_FIELD", "name").strip() or "name",
        "direct_db_fallback_to_responder": getenv_bool("DIRECT_DB_FALLBACK_TO_RESPONDER", False),
        "direct_db_delete_catch_command": getenv_bool("DIRECT_DB_DELETE_CATCH_COMMAND", getenv_bool("AUTO_DELETE_CATCH_COMMAND", True)),
        "direct_db_debug": getenv_bool("DIRECT_DB_DEBUG", True),
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


async def warmup_peer_cache(app: Optional[Client] = None, limit: int = 200) -> bool:
    """
    Pyrogram string sessions with in_memory=True may not have chat peer cache.
    get_dialogs() loads recent peers so numeric -100... chat IDs become sendable.
    """
    client = app or app_a or app_b
    log_group_id = CONFIG.get("log_group_id")

    if client is None or not log_group_id:
        return False

    try:
        async for dialog in client.get_dialogs(limit=limit):
            chat = dialog.chat
            if chat and chat.id == log_group_id:
                return True
    except Exception as e:
        logging.warning("warmup_peer_cache failed: %s", e)

    return False


async def send_log(text: str, parse_html: bool = False, app: Optional[Client] = None) -> None:
    client = app or app_a or app_b
    log_group_id = CONFIG.get("log_group_id")

    if client is None or not log_group_id:
        return

    async def _send_once():
        return await client.send_message(
            log_group_id,
            text,
            parse_mode=ParseMode.HTML if parse_html else None,
            disable_web_page_preview=True,
        )

    try:
        await _send_once()
    except FloodWait as e:
        logging.warning("send_log FloodWait: sleeping %s seconds", e.value)
        await asyncio.sleep(e.value)
    except Exception as e:
        if "Peer id invalid" in str(e):
            warmed = await warmup_peer_cache(client)
            if warmed:
                try:
                    await _send_once()
                    return
                except Exception as retry_error:
                    logging.warning("send_log retry failed: %s", retry_error)
                    return

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

    cursor.execute("""
        CREATE TABLE IF NOT EXISTS captcha_digit_templates (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            created_at TEXT,
            digit TEXT NOT NULL,
            template BLOB NOT NULL,
            width INTEGER NOT NULL DEFAULT 32,
            height INTEGER NOT NULL DEFAULT 32,
            answer TEXT,
            source_session TEXT,
            source_chat_id INTEGER,
            source_message_id INTEGER
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


def strip_invisible(text: str) -> str:
    if not text:
        return ""
    text = unicodedata.normalize("NFKC", text)
    text = re.sub(r"[\u200b-\u200f\u202a-\u202e\u2060\ufeff]", "", text)
    return text


def clean_catch_command(cmd: str) -> str:
    cmd = strip_invisible(cmd)
    cmd = cmd.replace("`", "").replace("<code>", "").replace("</code>", "")
    cmd = re.sub(r"\s+", " ", cmd).strip()

    # Stop at button/footer/noise lines if accidentally captured.
    cmd = re.split(
        r"\s+(?:Full|Powered|Copy|Official|Hint|NAME)\b",
        cmd,
        maxsplit=1,
        flags=re.IGNORECASE,
    )[0].strip()

    if not cmd.lower().startswith("/catch"):
        return ""
    return cmd


def extract_catch_command(response_text: str) -> Optional[str]:
    """
    Robustly extract catch command from responder bot reply.
    Supports:
      ❤️ Hint: /catch Douma
      Hint : /catch Douma
      Hint：/catch Douma
      Full: /catch Name [Extra]
      Any fallback /catch line
    """
    text = strip_invisible(response_text or "")
    if not text:
        return None

    text = (
        text.replace("：", ":")
        .replace("﹕", ":")
        .replace("꞉", ":")
        .replace("ꓽ", ":")
    )

    patterns = [
        r"(?:^|\n)[^\n]{0,60}?Hint\s*:\s*(/catch[^\n\r]+)",
        r"(?:^|\n)[^\n]{0,60}?Full\s*:\s*(/catch[^\n\r]+)",
        r"(/catch[^\n\r]+)",
    ]

    for pattern in patterns:
        match = re.search(pattern, text, flags=re.IGNORECASE)
        if match:
            cmd = clean_catch_command(match.group(1))
            if cmd:
                return cmd
    return None


def extract_catch_command_from_buttons(m) -> Optional[str]:
    """Try to read /catch from inline keyboard/copy-text buttons when text parsing fails."""
    try:
        markup = getattr(m, "reply_markup", None)
        keyboard = getattr(markup, "inline_keyboard", None)
        if not keyboard:
            return None

        for row in keyboard:
            for btn in row:
                values = []
                for attr in ("text", "url", "callback_data"):
                    value = getattr(btn, attr, None)
                    if value:
                        values.append(str(value))

                copy_text = getattr(btn, "copy_text", None)
                if copy_text:
                    values.append(str(copy_text))
                    value = getattr(copy_text, "text", None)
                    if value:
                        values.append(str(value))

                for value in values:
                    cmd = extract_catch_command(value)
                    if cmd:
                        return cmd
    except Exception as e:
        logging.warning("extract_catch_command_from_buttons failed: %s", e)

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


async def mark_spawn_processed(chat_id: int, message_id: int, session_key: str = "") -> bool:
    # Include session_key so AUTO_CATCH_SESSIONS=a,b can process once per session.
    # With AUTO_CATCH_SESSIONS=a, this behaves like a normal single-session dedupe.
    key = (session_key, chat_id, message_id)

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



# =========================
# DIRECT MONGODB CATCH LOOKUP
# =========================

def direct_db_base_filter() -> dict[str, Any]:
    return {
        "$or": [
            {"command_name": CONFIG.get("direct_db_command_name", "/catch")},
            {"source_bot_key": CONFIG.get("direct_db_source_bot_key", "catcher")},
        ]
    }


def get_media_object_and_type(m) -> tuple[Optional[Any], Optional[str]]:
    media_fields = [
        ("photo", "photo"),
        ("video", "video"),
        ("animation", "animation"),
        ("document", "document"),
        ("sticker", "sticker"),
    ]
    for attr, media_type in media_fields:
        media_obj = getattr(m, attr, None)
        if media_obj:
            return media_obj, media_type
    return None, None


def get_media_file_unique_id(m) -> Optional[str]:
    media_obj, _ = get_media_object_and_type(m)
    if not media_obj:
        return None
    return getattr(media_obj, "file_unique_id", None)


async def download_media_bytes(app: Client, m) -> Optional[bytes]:
    try:
        data = await app.download_media(m, in_memory=True)
    except Exception as e:
        logging.warning("direct db download_media failed: %s", e)
        return None

    if not data:
        return None

    if isinstance(data, BytesIO):
        return data.getvalue()
    if hasattr(data, "getbuffer"):
        return bytes(data.getbuffer())
    if isinstance(data, (bytes, bytearray)):
        return bytes(data)
    return None


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def compute_photo_phash_from_bytes(raw: bytes) -> Optional[str]:
    if Image is None or imagehash is None:
        return None
    try:
        img = Image.open(BytesIO(raw)).convert("RGB")
        return str(imagehash.phash(img))
    except Exception as e:
        logging.debug("compute phash failed: %s", e)
        return None


def hamming_hex_hash(a: str, b: str) -> int:
    try:
        return bin(int(str(a), 16) ^ int(str(b), 16)).count("1")
    except Exception:
        return 999


async def init_direct_db() -> None:
    global direct_mongo_client, direct_items_collection

    if not CONFIG.get("direct_db_catch_enabled"):
        return

    if AsyncIOMotorClient is None:
        await send_log("❌ Direct DB catch enabled but <code>motor</code> is not installed.", parse_html=True)
        return

    mongo_uri = CONFIG.get("direct_db_mongo_uri", "")
    db_name = CONFIG.get("direct_db_name", "")
    collection_name = CONFIG.get("direct_db_collection", "items")

    if not mongo_uri or not db_name:
        await send_log(
            "❌ Direct DB catch enabled but MONGO_URI/DIRECT_DB_MONGO_URI or DB_NAME/DIRECT_DB_NAME is missing.",
            parse_html=True,
        )
        return

    try:
        direct_mongo_client = AsyncIOMotorClient(mongo_uri, serverSelectionTimeoutMS=5000)
        await direct_mongo_client.admin.command("ping")
        direct_items_collection = direct_mongo_client[db_name][collection_name]

        # MongoDB is intentionally READ-ONLY here.
        # Do NOT create indexes or write any document/metadata from this userbot.
        # Use MongoDB Atlas/index management manually outside this bot if indexes are needed.
        await send_log(
            "✅ <b>Direct DB catch connected</b>\n"
            f"DB: <code>{html.escape(db_name)}</code>\n"
            f"Collection: <code>{html.escape(collection_name)}</code>\n"
            f"Sessions: <code>{html.escape(','.join(sorted(CONFIG.get('direct_db_sessions', []))))}</code>",
            parse_html=True,
        )
    except Exception as e:
        direct_items_collection = None
        logging.warning("init_direct_db failed: %s", e)
        await send_log(f"❌ Direct DB catch connect failed: <code>{html.escape(str(e))}</code>", parse_html=True)


async def direct_db_find_item(app: Client, m) -> tuple[Optional[dict[str, Any]], str]:
    if direct_items_collection is None:
        return None, "db_not_ready"

    base_filter = direct_db_base_filter()
    projection = {
        "name": 1,
        "hint": 1,
        "command": 1,
        "catch_command": 1,
        "command_name": 1,
        "source_bot_key": 1,
        "media_type": 1,
        "file_unique_id": 1,
        "sha256": 1,
        "phash": 1,
        "frame_hashes": 1,
        "card_id": 1,
        "anime_name": 1,
    }

    file_unique_id = get_media_file_unique_id(m)
    if CONFIG.get("direct_db_use_file_unique_id", True) and file_unique_id:
        doc = await direct_items_collection.find_one(
            {"$and": [base_filter, {"file_unique_id": file_unique_id}]},
            projection,
        )
        if doc:
            return doc, "file_unique_id"

    raw = None
    if CONFIG.get("direct_db_use_sha256", True) or CONFIG.get("direct_db_use_phash", False):
        raw = await download_media_bytes(app, m)

    if CONFIG.get("direct_db_use_sha256", True) and raw:
        digest = sha256_bytes(raw)
        doc = await direct_items_collection.find_one(
            {"$and": [base_filter, {"sha256": digest}]},
            projection,
        )
        if doc:
            return doc, "sha256"

    # Optional slow fallback for photos only. Keep OFF by default for speed.
    if CONFIG.get("direct_db_use_phash", False) and raw and getattr(m, "photo", None):
        current_phash = compute_photo_phash_from_bytes(raw)
        if current_phash:
            threshold = int(CONFIG.get("direct_db_phash_threshold", 8))
            scan_limit = int(CONFIG.get("direct_db_phash_scan_limit", 5000))
            cursor = direct_items_collection.find(
                {"$and": [base_filter, {"media_type": {"$in": ["photo", "image"]}}, {"phash": {"$exists": True, "$ne": None}}]},
                projection,
            ).limit(scan_limit)

            best_doc = None
            best_dist = 999
            async for doc in cursor:
                dist = hamming_hex_hash(current_phash, str(doc.get("phash", "")))
                if dist < best_dist:
                    best_dist = dist
                    best_doc = doc
                if dist == 0:
                    break

            if best_doc and best_dist <= threshold:
                best_doc["_phash_distance"] = best_dist
                return best_doc, f"phash:{best_dist}"

    return None, "not_found"


def strip_name_decorations(value: str) -> str:
    value = unicodedata.normalize("NFKC", value or "")
    value = re.sub(r"\[[^\]]*\]", " ", value)
    value = re.sub(r"[\u200b-\u200f\u202a-\u202e\u2060\ufeff]", "", value)
    value = re.sub(r"[🏀🎮💠🔵🟠🟣🟡💮⚜️❓]+", " ", value)
    return " ".join(value.split()).strip()


def build_direct_catch_command(doc: dict[str, Any]) -> Optional[str]:
    command_field = CONFIG.get("direct_db_command_field", "command")
    hint_field = CONFIG.get("direct_db_hint_field", "hint")
    name_field = CONFIG.get("direct_db_name_field", "name")
    command_name = str(doc.get("command_name") or CONFIG.get("direct_db_command_name", "/catch") or "/catch").strip()
    if not command_name.startswith("/"):
        command_name = "/catch"

    # 1) If DB already stores exact command, use it.
    for key in [command_field, "catch_command", "command"]:
        value = doc.get(key)
        if isinstance(value, str) and value.strip().lower().startswith(command_name.lower()):
            return clean_catch_command(value.strip()) or value.strip()

    # 2) Prefer stored hint if available.
    hint = str(doc.get(hint_field) or "").strip()
    if hint:
        hint = strip_name_decorations(hint)
        if hint:
            return f"{command_name} {hint}".strip()

    # 3) Build from name. Default mode = first token/hint, because most catcher bots accept short hint.
    name = strip_name_decorations(str(doc.get(name_field) or ""))
    if not name:
        return None

    mode = CONFIG.get("direct_db_name_mode", "hint")
    if mode in {"full", "name", "full_name"}:
        value = name
    else:
        value = name.split()[0]

    return f"{command_name} {value}".strip()


async def handle_direct_db_catch(app: Client, session_key: str, m, rarity: Optional[str], group_name: str) -> bool:
    if not CONFIG.get("direct_db_catch_enabled"):
        return False
    if session_key not in CONFIG.get("direct_db_sessions", {"a", "b"}):
        return False

    doc, method = await direct_db_find_item(app, m)
    if not doc:
        if CONFIG.get("direct_db_debug", True):
            await send_log(
                "🔎 <b>Direct DB no match</b>\n"
                f"Session: <code>{html.escape(session_key)}</code>\n"
                f"Method: <code>{html.escape(method)}</code>\n"
                f"Group: {html.escape(group_name)}\n"
                f"Group ID: <code>{m.chat.id}</code>",
                parse_html=True,
                app=app,
            )
        return False

    catch_command = build_direct_catch_command(doc)
    if not catch_command:
        await send_log(
            "❌ <b>Direct DB matched but command could not be built.</b>\n"
            f"Match method: <code>{html.escape(method)}</code>\n"
            f"Doc name: <code>{html.escape(str(doc.get('name')))}</code>",
            parse_html=True,
            app=app,
        )
        return False

    try:
        await asyncio.sleep(random.uniform(CONFIG["catch_min_delay"], CONFIG["catch_max_delay"]))
        sent_message = await app.send_message(m.chat.id, catch_command)

        pending_key = (session_key, -int(m.id))
        await add_pending_response(
            pending_key,
            {
                "session_key": session_key,
                "forwarded_message_id": -int(m.id),
                "original_message_id": m.id,
                "original_chat_id": m.chat.id,
                "character_name": str(doc.get("name") or "Unknown"),
                "rarity": rarity,
                "timestamp": now_local(),
                "waiting_for_result": True,
                "my_message_id": sent_message.id,
                "catch_command": catch_command,
                "direct_db": True,
            },
        )

        await send_log(
            "⚡ <b>Direct DB catch command sent</b>\n"
            f"Session: <code>{html.escape(session_key)}</code>\n"
            f"Character: {html.escape(str(doc.get('name') or 'Unknown'))}\n"
            f"Anime: {html.escape(str(doc.get('anime_name') or 'Unknown'))}\n"
            f"Rarity: {html.escape(str(rarity or 'Unknown'))}\n"
            f"Match: <code>{html.escape(method)}</code>\n"
            f"Command: <code>{html.escape(catch_command)}</code>\n"
            f"Group: {html.escape(group_name)}\n"
            f"Group ID: <code>{m.chat.id}</code>\n"
            f"⏰ Time: {html.escape(now_local_str('%H:%M:%S'))}",
            parse_html=True,
            app=app,
        )

        if CONFIG.get("direct_db_delete_catch_command", CONFIG.get("auto_delete_catch_command", True)):
            asyncio.create_task(
                delete_later(
                    app,
                    m.chat.id,
                    sent_message.id,
                    CONFIG.get("catch_delete_after_seconds", 1.0),
                )
            )

        return True

    except FloodWait as e:
        logging.warning("Direct DB catch FloodWait: sleeping %s seconds", e.value)
        await asyncio.sleep(e.value)
        return True
    except Exception as e:
        logging.warning("Direct DB catch send failed: %s", e)
        await send_log(f"❌ Direct DB catch send error: <code>{html.escape(str(e))}</code>", parse_html=True, app=app)
        return True



def get_message_sender_candidates(m) -> list[int]:
    """Return all sender-like ids Pyrogram may expose for bot/channel/forwarded posts."""
    ids: list[int] = []

    try:
        if getattr(m, "from_user", None) and m.from_user.id is not None:
            ids.append(int(m.from_user.id))
    except Exception:
        pass

    try:
        if getattr(m, "sender_chat", None) and m.sender_chat.id is not None:
            ids.append(int(m.sender_chat.id))
    except Exception:
        pass

    try:
        if getattr(m, "forward_from", None) and m.forward_from.id is not None:
            ids.append(int(m.forward_from.id))
    except Exception:
        pass

    try:
        if getattr(m, "forward_from_chat", None) and m.forward_from_chat.id is not None:
            ids.append(int(m.forward_from_chat.id))
    except Exception:
        pass

    seen: set[int] = set()
    out: list[int] = []
    for x in ids:
        if x not in seen:
            seen.add(x)
            out.append(x)
    return out


def is_source_bot_message(m) -> bool:
    bot_id = CONFIG.get("bot_id")
    if not bot_id:
        return False

    if not CONFIG.get("source_bot_strict", True):
        return bool((getattr(m, "from_user", None) and m.from_user.is_bot) or getattr(m, "sender_chat", None))

    return int(bot_id) in get_message_sender_candidates(m)


async def log_auto_skip_debug(app: Client, session_key: str, m, reason: str, extra: str = "") -> None:
    if not CONFIG.get("direct_db_debug", True):
        return
    try:
        text = get_message_text(m)
        if not is_character_spawn_text(text):
            return
        sender_ids = ",".join(str(x) for x in get_message_sender_candidates(m)) or "NONE"
        await send_log(
            "🧪 <b>Auto catch skipped</b>\n"
            f"Reason: <code>{html.escape(reason)}</code>\n"
            f"Session: <code>{html.escape(session_key)}</code>\n"
            f"Chat ID: <code>{getattr(getattr(m, 'chat', None), 'id', None)}</code>\n"
            f"Sender IDs: <code>{html.escape(sender_ids)}</code>\n"
            f"BOT_ID: <code>{html.escape(str(CONFIG.get('bot_id')))}</code>\n"
            f"{html.escape(extra)}",
            parse_html=True,
            app=app,
        )
    except Exception:
        pass


async def handle_auto_forward_spawn(app: Client, session_key: str, m) -> None:
    if not CONFIG.get("auto_forward_enabled"):
        return

    if session_key not in CONFIG.get("auto_catch_sessions", {"a", "b"}):
        return

    if auto_forward_paused or auto_forward_error:
        return

    bot_id = CONFIG.get("bot_id")
    responder_bot_id = CONFIG.get("responder_bot_id")

    if not bot_id:
        return

    if not responder_bot_id and not CONFIG.get("direct_db_catch_enabled"):
        return

    if not m.chat or not m.chat.id:
        return

    chat_id = m.chat.id

    if chat_id not in SOURCE_GROUPS_CONFIG:
        return

    if not is_group_enabled(chat_id):
        return

    message_text = get_message_text(m)

    if not is_source_bot_message(m):
        await log_auto_skip_debug(app, session_key, m, "sender_mismatch")
        return


    if await handle_attention_log(app, m, session_key):
        return

    if not is_character_spawn_text(message_text):
        return

    first_processor = await mark_spawn_processed(chat_id, m.id, session_key)
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

    if CONFIG.get("direct_db_catch_enabled"):
        direct_sent = await handle_direct_db_catch(app, session_key, m, rarity, group_name)
        if direct_sent:
            return
        if not CONFIG.get("direct_db_fallback_to_responder", False):
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
    """
    Convert responder bot DM into /catch command in the original group.

    Fixes for Waifu Cheat Bot:
    - Accept ChatType.BOT and ChatType.PRIVATE.
    - Broad early handler catches all messages; this function self-filters.
    - Allows RESPONDER_BOT_IDS list, but can still process any bot DM that contains /catch.
    - Reads /catch from message text and inline CopyTextButton fallback.
    - Falls back to latest pending spawn when NAME does not match pending NAME placeholder.
    """
    try:
        if not CONFIG.get("auto_forward_enabled"):
            return
        if auto_forward_paused or auto_forward_error:
            return
        if not m.chat or not getattr(m, "id", None):
            return
        if m.chat.type not in {ChatType.PRIVATE, ChatType.BOT}:
            return

        # Deduplicate because this function is called from an early responder handler and general handler.
        dedupe_key = (session_key, int(m.chat.id), int(m.id))
        async with responder_dm_lock:
            if dedupe_key in responder_dm_seen:
                return
            responder_dm_seen.add(dedupe_key)
            if len(responder_dm_seen) > 3000:
                responder_dm_seen.clear()

        response_text = get_message_text(m)
        catch_command = extract_catch_command(response_text)
        if not catch_command:
            catch_command = extract_catch_command_from_buttons(m)

        sender_id = m.from_user.id if m.from_user else None
        responder_ids = set(CONFIG.get("responder_bot_ids") or set())
        responder_bot_id = CONFIG.get("responder_bot_id")
        if responder_bot_id:
            responder_ids.add(int(responder_bot_id))

        is_known_responder = bool(sender_id and int(sender_id) in responder_ids)
        is_bot_sender = bool(m.from_user and m.from_user.is_bot)

        # Normal path: known responder bot. Fallback path: any bot DM containing /catch.
        if not is_known_responder and not (is_bot_sender and catch_command):
            return

        if CONFIG.get("debug_responder"):
            await send_log(
                "🧪 <b>Responder DM received</b>\n"
                f"Session: <code>{html.escape(session_key)}</code>\n"
                f"From: <code>{html.escape(str(sender_id))}</code>\n"
                f"Known responder: <code>{html.escape(str(is_known_responder))}</code>\n"
                f"Command: <code>{html.escape(str(catch_command or 'NOT_FOUND'))}</code>\n"
                f"Text:\n<code>{html.escape((response_text or '')[:700])}</code>",
                parse_html=True,
                app=app,
            )

        if not catch_command:
            return

        normalized_response = unicodedata.normalize("NFKC", response_text or "")
        name_match = re.search(
            r"(?:NAME|Name|Nᴀᴍᴇ|ɴᴀᴍᴇ)\s*[:：]\s*([^\n]+)",
            normalized_response,
            re.IGNORECASE,
        )
        character_name = name_match.group(1).strip() if name_match else "Unknown"
        character_name = re.sub(r"[\[\]🏀🎮]", "", character_name).strip() or "Unknown"

        pending_key, pending = await select_pending_response(session_key, character_name)

        # Waifu replies often have the real NAME while original post contains placeholder NAME.
        # If exact-name matching fails, use the latest non-waiting pending for this session.
        if not pending_key or not pending:
            await cleanup_stale_pending()
            async with pending_lock:
                candidates = [
                    (pid, item)
                    for pid, item in pending_responses.items()
                    if item.get("session_key") == session_key and not item.get("waiting_for_result")
                ]
                candidates.sort(key=lambda item: item[1].get("timestamp", now_local()), reverse=True)
                if candidates:
                    pending_key, pending = candidates[0]

        if not pending_key or not pending:
            await send_log(
                "⚠️ <b>Responder parsed but no pending spawn found</b>\n"
                f"Session: <code>{html.escape(session_key)}</code>\n"
                f"Character: <code>{html.escape(character_name)}</code>\n"
                f"Command: <code>{html.escape(catch_command)}</code>\n"
                f"Pending count: <code>{len(pending_responses)}</code>",
                parse_html=True,
                app=app,
            )
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
                f"Group ID: <code>{pending['original_chat_id']}</code>\n"
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
            logging.warning("handle_responder_dm send failed: %s", e)
            await send_log(
                f"❌ Catch command send error: <code>{html.escape(str(e))}</code>",
                parse_html=True,
                app=app,
            )

    except Exception as e:
        logging.warning("handle_responder_dm failed: %s", e)


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

    if not is_source_bot_message(m):
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
    if bot_id and not is_source_bot_message(m):
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



# =========================
# CAPTCHA AUTO-SOLVER
# =========================

def captcha_cv_ready() -> bool:
    return cv2 is not None and np is not None


def normalize_option(text: str | int) -> str:
    text = str(text or "").strip()
    if text.isdigit() and len(text) <= 4:
        return text.zfill(4)
    return text


def is_numeric_option(text: str) -> bool:
    return bool(re.fullmatch(r"\d{1,4}", str(text or "").strip()))


def extract_numeric_buttons_pyro(m) -> list[str]:
    options: list[str] = []
    rows = getattr(getattr(m, "reply_markup", None), "inline_keyboard", None)
    if not rows:
        return options
    for row in rows:
        for btn in row:
            text = normalize_option(getattr(btn, "text", "") or "")
            if is_numeric_option(text) and text not in options:
                options.append(text)
    return options


def looks_like_captcha_message(m) -> bool:
    if not CONFIG.get("captcha_solver_enabled"):
        return False
    if not m.chat or m.chat.id not in CONFIG.get("captcha_target_groups", set()):
        return False
    captcha_bot_id = CONFIG.get("captcha_bot_id")
    if captcha_bot_id and (not m.from_user or m.from_user.id != captcha_bot_id):
        return False
    if not getattr(m, "photo", None):
        return False
    options = extract_numeric_buttons_pyro(m)
    if len(options) < 2:
        return False
    text = get_message_text(m)
    normalized = normalize_text(text)
    return (
        "captcha" in normalized
        or "attention" in normalized
        or "solve" in normalized
        or "special character" in normalized
        or len(options) >= 3
    )


async def download_pyro_message_media_as_cv2(app: Client, m):
    if not captcha_cv_ready():
        return None
    try:
        data = await app.download_media(m, in_memory=True)
    except Exception as e:
        logging.warning("captcha download_media failed: %s", e)
        return None
    if not data:
        return None
    try:
        if isinstance(data, BytesIO):
            raw = data.getvalue()
        elif hasattr(data, "getbuffer"):
            raw = bytes(data.getbuffer())
        elif isinstance(data, (bytes, bytearray)):
            raw = bytes(data)
        else:
            return None
        arr = np.frombuffer(raw, dtype=np.uint8)
        return cv2.imdecode(arr, cv2.IMREAD_COLOR)
    except Exception as e:
        logging.warning("captcha cv2 decode failed: %s", e)
        return None


async def click_button_by_text_pyro(m, answer: str) -> bool:
    """
    Click the inline keyboard button whose visible text equals answer.

    Important: do NOT use row/column coordinates by default. In Pyrogram versions,
    coordinate order can be easy to mix up, which may click a different button even
    when the detected answer is correct. This function prefers exact text/callback
    clicking and only uses coordinate fallback when explicitly enabled.
    """
    answer = normalize_option(answer)
    rows = getattr(getattr(m, "reply_markup", None), "inline_keyboard", None)
    if not rows:
        logging.warning("captcha click skipped: no inline keyboard")
        return False

    matched_button = None
    matched_row = -1
    matched_col = -1

    for row_index, row in enumerate(rows):
        for col_index, btn in enumerate(row):
            btn_text = normalize_option(getattr(btn, "text", "") or "")
            if btn_text == answer:
                matched_button = btn
                matched_row = row_index
                matched_col = col_index
                break
        if matched_button is not None:
            break

    if matched_button is None:
        logging.warning("captcha click skipped: answer button not found | answer=%s", answer)
        return False

    # 1) Safest: send exact callback_data for the matched button.
    callback_data = getattr(matched_button, "callback_data", None)
    if callback_data:
        try:
            await m._client.request_callback_answer(
                chat_id=m.chat.id,
                message_id=m.id,
                callback_data=callback_data,
                timeout=10,
            )
            logging.warning(
                "captcha clicked by callback_data | answer=%s | row=%s col=%s",
                answer, matched_row, matched_col,
            )
            return True
        except Exception as e:
            logging.warning(
                "captcha callback_data click failed, trying text click | answer=%s | row=%s col=%s | error=%s",
                answer, matched_row, matched_col, e,
            )

    # 2) Safe fallback: let Pyrogram find button by exact text.
    # Different Pyrogram builds expose either positional text or keyword text.
    for attempt_name, call in (
        ("text_positional", lambda: m.click(answer)),
        ("text_keyword", lambda: m.click(text=answer)),
    ):
        try:
            result = call()
            if hasattr(result, "__await__"):
                await result
            logging.warning(
                "captcha clicked by %s | answer=%s | row=%s col=%s",
                attempt_name, answer, matched_row, matched_col,
            )
            return True
        except TypeError:
            continue
        except Exception as e:
            logging.warning(
                "captcha %s click failed | answer=%s | row=%s col=%s | error=%s",
                attempt_name, answer, matched_row, matched_col, e,
            )

    # 3) Unsafe coordinate fallback is disabled by default. Enable only if your
    # Pyrogram build cannot click by callback/text.
    if CONFIG.get("captcha_allow_coordinate_click", False):
        try:
            # Pyrogram coordinate order is x=column, y=row.
            await m.click(matched_col, matched_row)
            logging.warning(
                "captcha clicked by coordinate fallback | answer=%s | row=%s col=%s",
                answer, matched_row, matched_col,
            )
            return True
        except Exception as e:
            logging.warning(
                "captcha coordinate click failed | answer=%s | row=%s col=%s | error=%s",
                answer, matched_row, matched_col, e,
            )

    logging.warning("captcha click failed safely: no click method worked | answer=%s", answer)
    return False

# Plain image marker decoder: works only if your own captcha generator embeds it.
MARKER_MAGIC_BITS = [1, 0, 1, 1]
MARKER_ANSWER_BITS = 14
MARKER_TOTAL_BITS = len(MARKER_MAGIC_BITS) + MARKER_ANSWER_BITS
MARKER_CELL = int(os.getenv("MARKER_CELL", "6"))
MARKER_REPEAT = int(os.getenv("MARKER_REPEAT", "3"))
MARKER_START_X = int(os.getenv("MARKER_START_X", "6"))
MARKER_START_Y = int(os.getenv("MARKER_START_Y", "6"))
MARKER_THRESHOLD = int(os.getenv("MARKER_THRESHOLD", "128"))


def _bits_to_int(bits: list[int]) -> int:
    value = 0
    for bit in bits:
        value = (value << 1) | int(bit)
    return value


def _marker_positions(img_width: int) -> list[tuple[int, int]]:
    total_cells = MARKER_TOTAL_BITS * MARKER_REPEAT
    usable_width = img_width - MARKER_START_X - 4
    if usable_width < MARKER_CELL:
        return []
    cells_per_row = max(1, usable_width // MARKER_CELL)
    return [
        (
            MARKER_START_X + (i % cells_per_row) * MARKER_CELL,
            MARKER_START_Y + (i // cells_per_row) * MARKER_CELL,
        )
        for i in range(total_cells)
    ]


def decode_plain_answer_marker(img) -> Optional[tuple[str, float]]:
    if not captcha_cv_ready() or img is None or img.size == 0:
        return None
    h, w = img.shape[:2]
    positions = _marker_positions(w)
    if not positions:
        return None
    last_x, last_y = positions[-1]
    if last_y + MARKER_CELL > h or last_x + MARKER_CELL > w:
        return None

    gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
    raw_bits: list[int] = []
    raw_votes: list[float] = []

    for x, y in positions:
        crop = gray[y:y + MARKER_CELL, x:x + MARKER_CELL]
        if crop.size == 0:
            return None
        mean_value = float(crop.mean())
        raw_bits.append(1 if mean_value < MARKER_THRESHOLD else 0)
        raw_votes.append(min(1.0, abs(mean_value - MARKER_THRESHOLD) / 120.0))

    bits: list[int] = []
    confs: list[float] = []
    for i in range(0, len(raw_bits), MARKER_REPEAT):
        group = raw_bits[i:i + MARKER_REPEAT]
        group_conf = raw_votes[i:i + MARKER_REPEAT]
        one_count = sum(group)
        bits.append(1 if one_count >= ((MARKER_REPEAT // 2) + 1) else 0)
        agreement = max(one_count, MARKER_REPEAT - one_count) / max(1, MARKER_REPEAT)
        confs.append(float(agreement * (sum(group_conf) / max(1, len(group_conf)))))

    if bits[:len(MARKER_MAGIC_BITS)] != MARKER_MAGIC_BITS:
        return None

    answer_num = _bits_to_int(bits[len(MARKER_MAGIC_BITS):])
    if not (0 <= answer_num <= 9999):
        return None
    return str(answer_num).zfill(4), sum(confs) / max(1, len(confs))


def _clean_ocr_digits(text: str) -> str:
    return "".join(re.findall(r"\d", text or ""))


def _remove_colored_lines_keep_dark_digits(img):
    if not captcha_cv_ready():
        return img
    out = img.copy()
    hsv = cv2.cvtColor(out, cv2.COLOR_BGR2HSV)
    # Colored lines usually have saturation; black/gray digits have low saturation.
    mask = ((hsv[:, :, 1] > 35) & (hsv[:, :, 2] > 30)).astype("uint8") * 255
    mask = cv2.dilate(mask, np.ones((2, 2), np.uint8), iterations=1)
    out[mask > 0] = (255, 255, 255)
    return out


def _ocr_image_variants(img) -> list[Any]:
    variants: list[Any] = []
    if not captcha_cv_ready() or img is None:
        return variants

    cleaned_bgr = _remove_colored_lines_keep_dark_digits(img)
    for base in [img, cleaned_bgr]:
        gray = cv2.cvtColor(base, cv2.COLOR_BGR2GRAY)
        h, w = gray.shape[:2]
        y0 = min(8, max(0, h // 30))
        core = gray[y0:h - y0, 0:w]
        core = cv2.resize(core, None, fx=3.0, fy=3.0, interpolation=cv2.INTER_CUBIC)
        norm = cv2.normalize(core, None, 0, 255, cv2.NORM_MINMAX)
        variants.extend([core, norm])

        for thresh_type in [cv2.THRESH_BINARY, cv2.THRESH_BINARY_INV]:
            _, th = cv2.threshold(norm, 0, 255, thresh_type + cv2.THRESH_OTSU)
            variants.append(th)
            kernel = np.ones((2, 2), np.uint8)
            variants.append(cv2.morphologyEx(th, cv2.MORPH_OPEN, kernel))
            variants.append(cv2.morphologyEx(th, cv2.MORPH_CLOSE, kernel))

        try:
            variants.append(
                cv2.adaptiveThreshold(
                    norm,
                    255,
                    cv2.ADAPTIVE_THRESH_GAUSSIAN_C,
                    cv2.THRESH_BINARY,
                    31,
                    9,
                )
            )
        except Exception:
            pass

    return variants


def _score_candidate_from_text(text: str, options: list[str]) -> dict[str, float]:
    scores: dict[str, float] = {}
    digits = _clean_ocr_digits(text)
    if not digits:
        return scores

    possible: set[str] = set()
    if len(digits) >= 4:
        for i in range(0, len(digits) - 3):
            possible.add(normalize_option(digits[i:i + 4]))
    else:
        possible.add(normalize_option(digits[:4]))

    for candidate in possible:
        if candidate in options:
            scores[candidate] = scores.get(candidate, 0.0) + 1.0

    return scores


# Option-guided visual digit solver for line/noise captcha.
# This does not rely on OCR text. It extracts dark digit-like components,
# scores each component against built-in digit templates, then chooses the
# best answer from the actual Telegram button options.
_DIGIT_TEMPLATE_CACHE: Optional[dict[str, list[Any]]] = None


def _resize_digit_bitmap_to_square(binary, size: int = 32):
    if not captcha_cv_ready() or binary is None:
        return None

    if len(binary.shape) == 3:
        binary = cv2.cvtColor(binary, cv2.COLOR_BGR2GRAY)

    binary = (binary > 0).astype("uint8") * 255
    ys, xs = np.where(binary > 0)
    if len(xs) == 0:
        return np.zeros((size, size), dtype="uint8")

    crop = binary[ys.min():ys.max() + 1, xs.min():xs.max() + 1]
    h, w = crop.shape[:2]
    if h <= 0 or w <= 0:
        return np.zeros((size, size), dtype="uint8")

    scale = min((size - 4) / max(1, w), (size - 4) / max(1, h))
    new_w = max(1, int(w * scale))
    new_h = max(1, int(h * scale))
    resized = cv2.resize(crop, (new_w, new_h), interpolation=cv2.INTER_AREA)

    canvas = np.zeros((size, size), dtype="uint8")
    x0 = (size - new_w) // 2
    y0 = (size - new_h) // 2
    canvas[y0:y0 + new_h, x0:x0 + new_w] = resized
    return canvas


def _get_digit_template_cache() -> dict[str, list[Any]]:
    global _DIGIT_TEMPLATE_CACHE

    if _DIGIT_TEMPLATE_CACHE is not None:
        return _DIGIT_TEMPLATE_CACHE

    if not captcha_cv_ready():
        _DIGIT_TEMPLATE_CACHE = {}
        return _DIGIT_TEMPLATE_CACHE

    fonts = [
        cv2.FONT_HERSHEY_SIMPLEX,
        cv2.FONT_HERSHEY_PLAIN,
        cv2.FONT_HERSHEY_DUPLEX,
        cv2.FONT_HERSHEY_COMPLEX_SMALL,
        cv2.FONT_HERSHEY_TRIPLEX,
        cv2.FONT_HERSHEY_COMPLEX,
    ]

    cache: dict[str, list[Any]] = {str(i): [] for i in range(10)}
    for digit in cache.keys():
        for font in fonts:
            for scale in (1.0, 1.2, 1.4, 1.6, 1.8, 2.0):
                for thickness in (1, 2, 3):
                    canvas = np.zeros((80, 80), dtype="uint8")
                    (tw, th), _ = cv2.getTextSize(digit, font, scale, thickness)
                    x = max(0, (80 - tw) // 2)
                    y = max(th + 2, (80 + th) // 2)
                    cv2.putText(canvas, digit, (x, y), font, scale, 255, thickness, cv2.LINE_AA)

                    variants = [canvas]
                    variants.append(cv2.dilate(canvas, np.ones((2, 2), np.uint8), iterations=1))
                    variants.append(cv2.erode(canvas, np.ones((2, 2), np.uint8), iterations=1))

                    for variant in variants:
                        tpl = _resize_digit_bitmap_to_square(variant, 32)
                        if tpl is not None:
                            cache[digit].append(tpl)

    _DIGIT_TEMPLATE_CACHE = cache
    return _DIGIT_TEMPLATE_CACHE


def _score_digit_bitmap_against_templates(binary) -> dict[str, float]:
    scores: dict[str, float] = {}
    if not captcha_cv_ready() or binary is None:
        return scores

    roi = _resize_digit_bitmap_to_square(binary, 32)
    if roi is None:
        return scores

    roi_f = roi.astype("float32") / 255.0
    roi_b = roi_f > 0.20
    roi_norm = float(np.sqrt(np.sum(roi_f * roi_f)))

    templates = _get_digit_template_cache()
    for digit, digit_templates in templates.items():
        best = 0.0
        for template in digit_templates:
            tpl_f = template.astype("float32") / 255.0
            tpl_b = tpl_f > 0.20

            union = np.sum(roi_b | tpl_b)
            if union <= 0:
                iou = 0.0
            else:
                iou = float(np.sum(roi_b & tpl_b) / union)

            tpl_norm = float(np.sqrt(np.sum(tpl_f * tpl_f)))
            if roi_norm <= 1e-6 or tpl_norm <= 1e-6:
                corr = 0.0
            else:
                corr = float(np.sum(roi_f * tpl_f) / (roi_norm * tpl_norm + 1e-6))

            score = (0.50 * iou) + (0.50 * corr)
            if score > best:
                best = score

        scores[digit] = best

    return scores


def _extract_digit_components_from_mask(mask) -> list[tuple[int, int, int, int, int, float, float]]:
    components: list[tuple[int, int, int, int, int, float, float]] = []
    if not captcha_cv_ready() or mask is None:
        return components

    count, labels, stats, centroids = cv2.connectedComponentsWithStats(mask, 8)
    for idx in range(1, count):
        x, y, w, h, area = stats[idx]
        if area < 100:
            continue
        if not (10 <= w <= 60 and 18 <= h <= 60):
            continue
        if (w / max(1, h)) > 2.4 or (h / max(1, w)) > 3.8:
            continue
        density = float(area) / float(max(1, w * h))
        if density < 0.12 or density > 0.90:
            continue
        cx, cy = centroids[idx]
        components.append((int(x), int(y), int(w), int(h), int(area), float(cx), float(cy)))

    return components


def _choose_digit_component_group(components: list[tuple[int, int, int, int, int, float, float]], count_needed: int = 4):
    if len(components) < count_needed:
        return None

    import itertools

    top = sorted(components, key=lambda c: c[4], reverse=True)[:12]
    best_group = None
    best_value = -1e9

    for group in itertools.combinations(top, count_needed):
        group = sorted(group, key=lambda c: c[5])
        xs = [c[5] for c in group]
        ys = [c[6] for c in group]

        if len(xs) > 1 and min(np.diff(xs)) < 40:
            continue

        y_spread = max(ys) - min(ys)
        if y_spread > 120:
            continue

        x_spread = xs[-1] - xs[0] if len(xs) > 1 else 0
        value = sum(c[4] for c in group) - (2.0 * y_spread) + (0.03 * x_spread)
        if value > best_value:
            best_value = value
            best_group = group

    return list(best_group) if best_group else None



def _digit_binary_mask_from_image(img):
    """Return a dark-digit mask after trying to remove colored noise lines."""
    if not captcha_cv_ready() or img is None:
        return None

    hsv = cv2.cvtColor(img, cv2.COLOR_BGR2HSV)
    gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)

    # Digits are usually black/gray: low saturation + dark value.
    # Colored lines are higher saturation and should be suppressed.
    low_sat_dark = ((hsv[:, :, 1] < 95) & (hsv[:, :, 2] < 225)).astype("uint8") * 255

    # Very dark pixels should remain even if compression creates a little saturation.
    very_dark = (gray < 155).astype("uint8") * 255
    mask = cv2.bitwise_or(low_sat_dark, very_dark)

    # Remove colored line remnants.
    colored = ((hsv[:, :, 1] > 45) & (hsv[:, :, 2] > 45)).astype("uint8") * 255
    colored = cv2.dilate(colored, np.ones((2, 2), np.uint8), iterations=1)
    mask[colored > 0] = 0

    # Clean tiny specks but keep thin digit strokes.
    mask = cv2.medianBlur(mask, 3)
    mask = cv2.morphologyEx(mask, cv2.MORPH_CLOSE, np.ones((2, 2), np.uint8), iterations=1)
    return mask


def _extract_digit_candidates_relaxed(mask):
    """Return candidate digit components sorted left-to-right."""
    candidates = []
    if not captcha_cv_ready() or mask is None:
        return candidates

    count, labels, stats, centroids = cv2.connectedComponentsWithStats(mask, 8)
    h_img, w_img = mask.shape[:2]

    for idx in range(1, count):
        x, y, w, h, area = stats[idx]
        if area < 12:
            continue
        if w < 3 or h < 7:
            continue
        if w > 90 or h > 90:
            continue
        # Ignore long line fragments.
        aspect = w / max(1, h)
        if aspect > 3.5 or aspect < 0.08:
            continue
        density = float(area) / float(max(1, w * h))
        if density < 0.05 or density > 0.95:
            continue
        cx, cy = centroids[idx]
        candidates.append((int(x), int(y), int(w), int(h), int(area), float(cx), float(cy)))

    # Merge very close small fragments that are likely broken pieces of a digit.
    candidates.sort(key=lambda c: c[5])
    merged = []
    used = [False] * len(candidates)
    for i, c in enumerate(candidates):
        if used[i]:
            continue
        x1, y1, w1, h1, area1, cx1, cy1 = c
        box = [x1, y1, x1 + w1, y1 + h1]
        total_area = area1
        centers = [(cx1, cy1, area1)]
        used[i] = True
        for j in range(i + 1, len(candidates)):
            if used[j]:
                continue
            x2, y2, w2, h2, area2, cx2, cy2 = candidates[j]
            # close horizontally and vertically: broken same digit
            if abs(cx2 - cx1) <= 18 and abs(cy2 - cy1) <= 28:
                box[0] = min(box[0], x2); box[1] = min(box[1], y2)
                box[2] = max(box[2], x2 + w2); box[3] = max(box[3], y2 + h2)
                total_area += area2
                centers.append((cx2, cy2, area2))
                used[j] = True
        bx, by, bx2, by2 = box
        bw, bh = bx2 - bx, by2 - by
        if total_area >= 18 and 3 <= bw <= 80 and 8 <= bh <= 80:
            cx = sum(a * x for x, y, a in centers) / max(1, total_area)
            cy = sum(a * y for x, y, a in centers) / max(1, total_area)
            merged.append((int(bx), int(by), int(bw), int(bh), int(total_area), float(cx), float(cy)))

    return sorted(merged, key=lambda c: c[5])


def _choose_four_digit_candidates(candidates):
    if len(candidates) < 4:
        return None
    import itertools

    # Keep the largest + most central candidates. Captcha digits are usually among biggest dark components.
    top = sorted(candidates, key=lambda c: c[4], reverse=True)[:16]
    best = None
    best_score = -1e18
    for group in itertools.combinations(top, 4):
        group = sorted(group, key=lambda c: c[5])
        xs = [c[5] for c in group]
        ys = [c[6] for c in group]
        if min(np.diff(xs)) < 35:
            continue
        y_spread = max(ys) - min(ys)
        if y_spread > 170:
            continue
        # Prefer reasonable digit areas and broad left-to-right spacing.
        areas = [c[4] for c in group]
        score = sum(areas) - 1.2 * y_spread + 0.01 * (xs[-1] - xs[0])
        if score > best_score:
            best_score = score
            best = group
    return list(best) if best else None


def _read_digits_by_single_char_tesseract(img, group) -> list[str]:
    """Optional per-digit Tesseract pass. Returns best digit per component; blank if unavailable."""
    try:
        import pytesseract
    except Exception:
        return []
    if not captcha_cv_ready() or img is None or not group:
        return []

    gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
    out = []
    for x, y, w, h, area, cx, cy in group:
        pad = 12
        crop = gray[max(0, y - pad):min(gray.shape[0], y + h + pad), max(0, x - pad):min(gray.shape[1], x + w + pad)]
        if crop.size == 0:
            out.append("")
            continue
        crop = cv2.resize(crop, None, fx=5.0, fy=5.0, interpolation=cv2.INTER_CUBIC)
        # Make dark digit on white background.
        _, th = cv2.threshold(crop, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)
        try:
            txt = pytesseract.image_to_string(
                th,
                config="--psm 10 --oem 3 -c tessedit_char_whitelist=0123456789",
            )
        except Exception:
            txt = ""
        digits = re.findall(r"\d", txt or "")
        out.append(digits[0] if digits else "")
    return out



def _template_to_blob(template) -> bytes:
    if not captcha_cv_ready() or template is None:
        return b""
    tpl = _resize_digit_bitmap_to_square(template, 32)
    if tpl is None:
        return b""
    return tpl.astype("uint8").tobytes()


def _blob_to_template(blob: bytes):
    if not captcha_cv_ready() or not blob:
        return None
    try:
        arr = np.frombuffer(blob, dtype=np.uint8)
        if arr.size != 32 * 32:
            return None
        return arr.reshape((32, 32)).copy()
    except Exception:
        return None


def _similarity_to_template_set(binary, templates: list[Any]) -> float:
    if not captcha_cv_ready() or binary is None or not templates:
        return 0.0
    roi = _resize_digit_bitmap_to_square(binary, 32)
    if roi is None:
        return 0.0
    roi_f = roi.astype("float32") / 255.0
    roi_b = roi_f > 0.20
    roi_norm = float(np.sqrt(np.sum(roi_f * roi_f)))
    best = 0.0
    for template in templates:
        if template is None:
            continue
        tpl_f = template.astype("float32") / 255.0
        tpl_b = tpl_f > 0.20
        union = np.sum(roi_b | tpl_b)
        iou = float(np.sum(roi_b & tpl_b) / union) if union > 0 else 0.0
        tpl_norm = float(np.sqrt(np.sum(tpl_f * tpl_f)))
        corr = 0.0 if roi_norm <= 1e-6 or tpl_norm <= 1e-6 else float(np.sum(roi_f * tpl_f) / (roi_norm * tpl_norm + 1e-6))
        score = (0.60 * iou) + (0.40 * corr)
        if score > best:
            best = score
    return best


async def _count_captcha_templates() -> tuple[int, dict[str, int]]:
    rows = await db_fetchall("SELECT digit, COUNT(*) FROM captcha_digit_templates GROUP BY digit")
    counts = {str(d): int(c) for d, c in rows}
    return sum(counts.values()), counts


def _load_learned_digit_templates_sync() -> dict[str, list[Any]]:
    global _LEARNED_DIGIT_TEMPLATE_CACHE
    if _LEARNED_DIGIT_TEMPLATE_CACHE is not None:
        return _LEARNED_DIGIT_TEMPLATE_CACHE
    cache: dict[str, list[Any]] = {str(i): [] for i in range(10)}
    if db_conn is None or not captcha_cv_ready():
        _LEARNED_DIGIT_TEMPLATE_CACHE = cache
        return cache
    try:
        cur = db_conn.cursor()
        cur.execute("SELECT digit, template FROM captcha_digit_templates ORDER BY id DESC LIMIT 3000")
        for digit, blob in cur.fetchall():
            digit = str(digit)
            if digit not in cache:
                continue
            tpl = _blob_to_template(blob)
            if tpl is not None:
                cache[digit].append(tpl)
    except Exception as e:
        logging.warning("load learned captcha templates failed: %s", e)
    _LEARNED_DIGIT_TEMPLATE_CACHE = cache
    return cache


def _extract_four_digit_crops_for_learning(img) -> Optional[list[Any]]:
    if not captcha_cv_ready() or img is None:
        return None
    masks = []
    main_mask = _digit_binary_mask_from_image(img)
    if main_mask is not None:
        masks.append(main_mask)
    gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
    hsv = cv2.cvtColor(img, cv2.COLOR_BGR2HSV)
    for gray_thr in (145, 165, 185, 205):
        mask = (gray < gray_thr).astype("uint8") * 255
        colored = ((hsv[:, :, 1] > 60) & (hsv[:, :, 2] > 45)).astype("uint8") * 255
        colored = cv2.dilate(colored, np.ones((2, 2), np.uint8), iterations=1)
        mask[colored > 0] = 0
        mask = cv2.medianBlur(mask, 3)
        masks.append(mask)
    best_group = None
    best_mask = None
    best_score = -1e18
    for mask in masks:
        comps = _extract_digit_candidates_relaxed(mask)
        group = _choose_four_digit_candidates(comps)
        if not group:
            continue
        areas = [c[4] for c in group]
        ys = [c[6] for c in group]
        xs = [c[5] for c in group]
        score = sum(areas) - 1.4 * (max(ys) - min(ys)) + 0.02 * (max(xs) - min(xs))
        if score > best_score:
            best_score = score
            best_group = group
            best_mask = mask
    if not best_group or best_mask is None:
        return None
    crops = []
    for x, y, w, h, area, cx, cy in sorted(best_group, key=lambda c: c[5]):
        pad = 10
        crop = best_mask[max(0, y - pad):min(best_mask.shape[0], y + h + pad), max(0, x - pad):min(best_mask.shape[1], x + w + pad)]
        if crop.size == 0:
            return None
        ys, xs = np.where(crop > 0)
        if len(xs) > 0:
            crop = crop[ys.min():ys.max() + 1, xs.min():xs.max() + 1]
        tpl = _resize_digit_bitmap_to_square(crop, 32)
        if tpl is None:
            return None
        crops.append(tpl)
    return crops if len(crops) == 4 else None


async def save_learned_captcha_templates_from_image(img, answer: str, session_key: str, chat_id: int, message_id: int) -> bool:
    global _LEARNED_DIGIT_TEMPLATE_CACHE
    if not CONFIG.get("captcha_learning_enabled", True):
        return False
    answer = normalize_option(answer)
    if not re.fullmatch(r"\d{4}", answer):
        return False
    crops = _extract_four_digit_crops_for_learning(img)
    if not crops or len(crops) != 4:
        await send_log(
            "⚠️ <b>Captcha learning failed.</b>\n"
            f"Answer: <code>{html.escape(answer)}</code>\n"
            "Reason: <code>could not segment 4 digits</code>",
            parse_html=True,
        )
        return False
    limit = int(CONFIG.get("captcha_learn_template_limit_per_digit", 200))
    async with db_lock:
        if db_conn is None:
            return False
        cur = db_conn.cursor()
        for digit, crop in zip(answer, crops):
            blob = _template_to_blob(crop)
            if not blob:
                continue
            cur.execute(
                """
                INSERT INTO captcha_digit_templates
                (created_at, digit, template, width, height, answer, source_session, source_chat_id, source_message_id)
                VALUES (?, ?, ?, 32, 32, ?, ?, ?, ?)
                """,
                (now_local_str(), digit, blob, answer, session_key, int(chat_id), int(message_id)),
            )
            cur.execute(
                """
                DELETE FROM captcha_digit_templates
                WHERE digit = ? AND id NOT IN (
                    SELECT id FROM captcha_digit_templates
                    WHERE digit = ? ORDER BY id DESC LIMIT ?
                )
                """,
                (digit, digit, limit),
            )
        db_conn.commit()
    _LEARNED_DIGIT_TEMPLATE_CACHE = None
    return True


def solve_by_learned_template_match(img, options: list[str]) -> Optional[tuple[str, float, str]]:
    if not captcha_cv_ready() or img is None:
        return None
    options = [normalize_option(x) for x in options if is_numeric_option(str(x))]
    options = [x for x in options if len(x) == 4]
    if not options:
        return None
    cache = _load_learned_digit_templates_sync()
    min_templates = int(CONFIG.get("captcha_learning_min_templates", 3))
    required_digits = set("".join(options))
    missing = [d for d in sorted(required_digits) if len(cache.get(d, [])) < min_templates]
    if missing:
        return None
    crops = _extract_four_digit_crops_for_learning(img)
    if not crops or len(crops) != 4:
        return None
    per_position_scores = []
    for crop in crops:
        pos_scores = {str(i): _similarity_to_template_set(crop, cache.get(str(i), [])) for i in range(10)}
        per_position_scores.append(pos_scores)
    option_scores: list[tuple[str, float, list[float]]] = []
    for option in options:
        parts = [per_position_scores[i].get(option[i], 0.0) for i in range(4)]
        weak_penalty = sum(1 for p in parts if p < 0.28) * 0.06
        score = float(sum(parts) / 4.0) - weak_penalty
        option_scores.append((option, score, parts))
    option_scores.sort(key=lambda x: x[1], reverse=True)
    if not option_scores:
        return None
    top_answer, top_score, top_parts = option_scores[0]
    second_score = option_scores[1][1] if len(option_scores) > 1 else 0.0
    margin = top_score - second_score
    if top_score < 0.36 or margin < 0.04:
        return None
    confidence = min(0.98, 0.52 + 0.38 * max(0.0, top_score) + 0.90 * min(0.30, max(0.0, margin)))
    return top_answer, confidence, f"learned_template_match:parts={[round(x,3) for x in top_parts]},margin={margin:.3f}"

def solve_by_visual_option_match(img, options: list[str]) -> Optional[tuple[str, float, str]]:
    """
    Strong captcha solver using the button options as constraints.
    It does not need to OCR a perfect 4-digit string. It detects four digit-like
    components, scores each against digit templates, then chooses the best option.
    """
    if not captcha_cv_ready() or img is None:
        return None

    options = [normalize_option(x) for x in options if is_numeric_option(str(x))]
    options = [x for x in options if len(x) == 4]
    if not options:
        return None

    masks = []
    main_mask = _digit_binary_mask_from_image(img)
    if main_mask is not None:
        masks.append(main_mask)

    # Extra threshold variants. Some Telegram-compressed captchas make digits lighter.
    hsv = cv2.cvtColor(img, cv2.COLOR_BGR2HSV)
    gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
    for sat_max, value_max in ((110, 235), (130, 235), (95, 245), (160, 210)):
        mask = ((hsv[:, :, 1] < sat_max) & (hsv[:, :, 2] < value_max)).astype("uint8") * 255
        colored = ((hsv[:, :, 1] > 55) & (hsv[:, :, 2] > 55)).astype("uint8") * 255
        colored = cv2.dilate(colored, np.ones((2, 2), np.uint8), iterations=1)
        mask[colored > 0] = 0
        mask = cv2.medianBlur(mask, 3)
        masks.append(mask)
    masks.append((gray < 190).astype("uint8") * 255)

    best_answer = None
    best_score = 0.0
    best_margin = 0.0
    best_method = "visual_option_match"

    for mask in masks:
        components = _extract_digit_candidates_relaxed(mask)
        group = _choose_four_digit_candidates(components)
        if not group:
            continue

        per_position_scores: list[dict[str, float]] = []
        for x, y, w, h, area, cx, cy in group:
            pad = 8
            crop = mask[max(0, y - pad):min(mask.shape[0], y + h + pad), max(0, x - pad):min(mask.shape[1], x + w + pad)]
            ys, xs = np.where(crop > 0)
            if len(xs) > 0:
                crop = crop[ys.min():ys.max() + 1, xs.min():xs.max() + 1]
            scores = _score_digit_bitmap_against_templates(crop)
            per_position_scores.append(scores)

        # Add a small boost from per-character Tesseract if available.
        char_tess = _read_digits_by_single_char_tesseract(img, group) if CONFIG.get("enable_tesseract_ocr", True) else []
        if len(char_tess) == 4:
            for idx, d in enumerate(char_tess):
                if d and idx < len(per_position_scores):
                    per_position_scores[idx][d] = max(per_position_scores[idx].get(d, 0.0), 0.95)

        candidate_scores: list[tuple[str, float, list[float]]] = []
        for option in options:
            parts = [per_position_scores[pos].get(ch, 0.0) for pos, ch in enumerate(option)]
            # Penalize any impossible/very weak digit, but do not reject immediately.
            weak_penalty = sum(1 for p in parts if p < 0.18) * 0.08
            score = float(sum(parts) / 4.0) - weak_penalty
            candidate_scores.append((option, score, parts))

        candidate_scores.sort(key=lambda item: item[1], reverse=True)
        top_answer, top_score, top_parts = candidate_scores[0]
        second_score = candidate_scores[1][1] if len(candidate_scores) > 1 else 0.0
        margin = top_score - second_score
        quality = top_score + (0.75 * margin)

        if best_answer is None or quality > (best_score + 0.75 * best_margin):
            best_answer = top_answer
            best_score = top_score
            best_margin = margin
            best_method = "visual_option_match"

    if not best_answer:
        return None

    # More permissive than before because button-options constraint reduces risk.
    if best_score < 0.25 or best_margin < 0.015:
        logging.info(
            "visual_option_match weak result answer=%s score=%.3f margin=%.3f",
            best_answer,
            best_score,
            best_margin,
        )
        return None

    confidence = min(0.94, 0.58 + 0.30 * max(0.0, best_score) + 0.80 * min(0.35, max(0.0, best_margin)))
    return best_answer, confidence, best_method


def solve_by_tesseract(img, options: list[str]) -> Optional[tuple[str, float, str]]:
    if not CONFIG.get("enable_ocr_fallback", True):
        return None
    if not CONFIG.get("enable_tesseract_ocr", True):
        return None
    if not captcha_cv_ready():
        return None
    try:
        import pytesseract
    except Exception:
        return None

    options = [normalize_option(x) for x in options]
    scores: dict[str, float] = {}

    for variant in _ocr_image_variants(img):
        for psm in [6, 7, 11, 13]:
            try:
                text = pytesseract.image_to_string(
                    variant,
                    config=f"--psm {psm} --oem 3 -c tessedit_char_whitelist=0123456789",
                )
            except Exception:
                continue

            for candidate, score in _score_candidate_from_text(text, options).items():
                scores[candidate] = scores.get(candidate, 0.0) + score

    if not scores:
        return None

    best, best_score = max(scores.items(), key=lambda kv: kv[1])
    total = sum(scores.values())
    confidence = min(0.88, 0.45 + 0.43 * (best_score / max(1.0, total)))
    return best, confidence, "tesseract_ocr"


def _get_easyocr_reader():
    global easyocr_reader
    if easyocr_reader is not None:
        return easyocr_reader
    try:
        import easyocr
        easyocr_reader = easyocr.Reader(["en"], gpu=False, verbose=False)
        return easyocr_reader
    except Exception as e:
        logging.warning("easyocr unavailable: %s", e)
        return None


def solve_by_easyocr(img, options: list[str]) -> Optional[tuple[str, float, str]]:
    if not CONFIG.get("enable_ocr_fallback", True):
        return None
    if not CONFIG.get("enable_easyocr", False):
        return None
    if not captcha_cv_ready():
        return None

    reader = _get_easyocr_reader()
    if reader is None:
        return None

    options = [normalize_option(x) for x in options]
    scores: dict[str, float] = {}

    for variant in _ocr_image_variants(img)[:8]:
        try:
            results = reader.readtext(variant, allowlist="0123456789", detail=1, paragraph=False)
        except Exception:
            continue

        for item in results:
            try:
                text = item[1]
                conf = float(item[2])
            except Exception:
                continue

            for candidate, score in _score_candidate_from_text(text, options).items():
                scores[candidate] = scores.get(candidate, 0.0) + max(0.2, conf) * score

    if not scores:
        return None

    best, best_score = max(scores.items(), key=lambda kv: kv[1])
    total = sum(scores.values())
    confidence = min(0.92, 0.50 + 0.42 * (best_score / max(1.0, total)))
    return best, confidence, "easyocr_ocr"


def vote_ocr_results(results: list[tuple[str, float, str]], options: list[str]) -> Optional[tuple[str, float, str]]:
    if not results:
        return None

    options = [normalize_option(x) for x in options]
    scores: dict[str, float] = {}
    methods: dict[str, list[str]] = {}

    for answer, confidence, method in results:
        answer = normalize_option(answer)
        if answer not in options:
            continue
        scores[answer] = scores.get(answer, 0.0) + max(0.01, confidence)
        methods.setdefault(answer, []).append(method)

    if not scores:
        return None

    best, score = max(scores.items(), key=lambda kv: kv[1])
    total = sum(scores.values())
    method_count = len(set(methods.get(best, [])))
    confidence = min(0.95, 0.50 + 0.30 * (score / max(0.01, total)) + 0.07 * method_count)
    return best, confidence, "ocr_vote:" + "+".join(sorted(set(methods.get(best, []))))



def _format_captcha_guess(answer: Optional[str], confidence: float, method: str, detail: str = "") -> str:
    if not answer:
        return "Best guess: <code>None</code>"
    line = (
        f"Best guess: <code>{html.escape(str(answer))}</code> "
        f"(<code>{confidence * 100:.1f}%</code>)\n"
        f"Guess method: <code>{html.escape(str(method))}</code>"
    )
    if detail:
        line += f"\nGuess detail: <code>{html.escape(str(detail)[:500])}</code>"
    return line


def _format_candidate_ranking(candidates: list[tuple[str, float, str]], limit: int = 5) -> str:
    cleaned = []
    seen = set()
    for answer, confidence, method in sorted(candidates, key=lambda x: x[1], reverse=True):
        answer = normalize_option(answer)
        if not answer or answer in seen:
            continue
        seen.add(answer)
        cleaned.append((answer, confidence, method))
        if len(cleaned) >= limit:
            break
    if not cleaned:
        return ""
    return " | ".join(f"{a}:{c * 100:.1f}%" for a, c, _ in cleaned)


def _score_options_by_quadrant_templates(img, options: list[str]) -> list[tuple[str, float, str]]:
    """
    OCR ထက်ပိုတည်ငြိမ်အောင် button options ကို constraint အဖြစ်သုံးတဲ့ visual matcher.
    Captcha image ကို x-axis ၄ ပိုင်းခွဲပြီး digit တစ်လုံးချင်း template similarity နဲ့ score ပေးတယ်။
    This returns ranked guesses even when confidence is weak, so logs can show the best attempt.
    """
    if not captcha_cv_ready() or img is None:
        return []

    options = [normalize_option(x) for x in options if is_numeric_option(str(x))]
    options = [x for x in options if len(x) == 4]
    if not options:
        return []

    h_img, w_img = img.shape[:2]
    if h_img <= 0 or w_img <= 0:
        return []

    gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
    hsv = cv2.cvtColor(img, cv2.COLOR_BGR2HSV)

    masks: list[Any] = []
    base = _digit_binary_mask_from_image(img)
    if base is not None:
        masks.append(base)

    # Several masks: some captchas compress digits lighter/darker.
    for gray_thr in (135, 155, 175, 195, 215):
        mask = (gray < gray_thr).astype("uint8") * 255
        # remove strongly colored line pixels; keep dark/gray digits.
        colored = ((hsv[:, :, 1] > 55) & (hsv[:, :, 2] > 45)).astype("uint8") * 255
        colored = cv2.dilate(colored, np.ones((2, 2), np.uint8), iterations=1)
        mask[colored > 0] = 0
        mask = cv2.medianBlur(mask, 3)
        masks.append(mask)

    for sat_max, val_max in ((80, 230), (100, 235), (130, 240), (160, 220)):
        mask = ((hsv[:, :, 1] < sat_max) & (hsv[:, :, 2] < val_max)).astype("uint8") * 255
        colored = ((hsv[:, :, 1] > 60) & (hsv[:, :, 2] > 50)).astype("uint8") * 255
        colored = cv2.dilate(colored, np.ones((2, 2), np.uint8), iterations=1)
        mask[colored > 0] = 0
        mask = cv2.medianBlur(mask, 3)
        masks.append(mask)

    ranked: dict[str, float] = {opt: 0.0 for opt in options}
    best_debug = ""

    for mask_idx, mask in enumerate(masks):
        if mask is None:
            continue

        per_position_scores: list[dict[str, float]] = []
        component_debug = []

        for pos in range(4):
            # digits are generally placed left-to-right in four broad zones
            x1 = int(w_img * pos / 4)
            x2 = int(w_img * (pos + 1) / 4)
            pad_x = int(w_img * 0.035)
            zx1 = max(0, x1 - pad_x)
            zx2 = min(w_img, x2 + pad_x)
            zone = mask[:, zx1:zx2]

            pos_scores: dict[str, float] = {str(i): 0.0 for i in range(10)}
            if zone.size == 0:
                per_position_scores.append(pos_scores)
                component_debug.append("none")
                continue

            count, labels, stats, centroids = cv2.connectedComponentsWithStats(zone, 8)
            components = []
            for idx in range(1, count):
                x, y, w, h, area = stats[idx]
                if area < 8 or area > 1800:
                    continue
                if w < 2 or h < 6 or w > 100 or h > 100:
                    continue
                aspect = float(w) / float(max(1, h))
                if aspect > 4.0 or aspect < 0.05:
                    continue
                density = float(area) / float(max(1, w * h))
                if density < 0.035 or density > 0.98:
                    continue
                # Ignore border fragments and far scattered dust where possible.
                cy = float(centroids[idx][1])
                if cy < 15 or cy > h_img - 15:
                    continue
                components.append((int(x), int(y), int(w), int(h), int(area), float(centroids[idx][0]), cy))

            # Largest several components in this zone; digit strokes are usually among them.
            components = sorted(components, key=lambda c: c[4], reverse=True)[:8]
            component_debug.append(str(len(components)))

            for x, y, w, h, area, cx, cy in components:
                pad = 10
                crop = zone[max(0, y - pad):min(zone.shape[0], y + h + pad), max(0, x - pad):min(zone.shape[1], x + w + pad)]
                if crop.size == 0:
                    continue
                ys, xs = np.where(crop > 0)
                if len(xs) > 0:
                    crop = crop[ys.min():ys.max() + 1, xs.min():xs.max() + 1]
                scores = _score_digit_bitmap_against_templates(crop)
                for digit, score in scores.items():
                    # More weight for bigger component; small dust should not dominate.
                    weighted = float(score) * min(1.0, max(0.25, area / 80.0))
                    if weighted > pos_scores.get(digit, 0.0):
                        pos_scores[digit] = weighted

            per_position_scores.append(pos_scores)

        # Score each actual Telegram button option using the per-position visual scores.
        option_scores: list[tuple[str, float, list[float]]] = []
        for opt in options:
            parts = [per_position_scores[i].get(opt[i], 0.0) for i in range(4)]
            missing = sum(1 for p in parts if p < 0.08)
            avg = float(sum(parts) / 4.0)
            score = avg - (missing * 0.045)
            option_scores.append((opt, score, parts))

        option_scores.sort(key=lambda x: x[1], reverse=True)
        if not option_scores:
            continue

        top_answer, top_score, top_parts = option_scores[0]
        second_score = option_scores[1][1] if len(option_scores) > 1 else 0.0
        margin = top_score - second_score
        confidence = max(0.01, min(0.88, 0.16 + (0.62 * max(0.0, top_score)) + (0.90 * max(0.0, min(margin, 0.35)))))

        # Aggregate per option across masks; max is more useful than average for noisy masks.
        if confidence > ranked.get(top_answer, 0.0):
            ranked[top_answer] = confidence
            best_debug = f"mask={mask_idx}, parts={[round(x, 3) for x in top_parts]}, margin={margin:.3f}, comps={','.join(component_debug)}"

    candidates = [(opt, conf, "visual_quadrant_match") for opt, conf in ranked.items() if conf > 0.01]
    candidates.sort(key=lambda x: x[1], reverse=True)
    # Attach debug to the top method name lightly without changing tuple shape.
    if candidates and best_debug:
        a, c, mth = candidates[0]
        candidates[0] = (a, c, mth + ":" + best_debug)
    return candidates


def solve_by_quadrant_option_match(img, options: list[str]) -> Optional[tuple[str, float, str]]:
    candidates = _score_options_by_quadrant_templates(img, options)
    if not candidates:
        return None
    answer, confidence, method = candidates[0]
    # Return only if confidence is reasonable; lower guesses are only for logging.
    if confidence < 0.34:
        return None
    return answer, confidence, method


def get_captcha_best_guess(img, options: list[str]) -> Optional[tuple[str, float, str, str]]:
    """Return best guess + confidence + method + ranked candidates, even if too weak for auto-click."""
    if not captcha_cv_ready() or img is None:
        return None

    options = [normalize_option(x) for x in options]
    candidates: list[tuple[str, float, str]] = []

    marker = decode_plain_answer_marker(img)
    if marker:
        answer, conf = marker
        if answer in options:
            candidates.append((answer, min(0.99, max(0.85, conf)), "plain_image_marker"))

    try:
        learned = solve_by_learned_template_match(img, options)
        if learned:
            candidates.append(learned)
    except Exception:
        pass

    try:
        visual = solve_by_visual_option_match(img, options)
        if visual:
            candidates.append(visual)
    except Exception:
        pass

    try:
        candidates.extend(_score_options_by_quadrant_templates(img, options)[:5])
    except Exception as e:
        logging.warning("quadrant best guess failed: %s", e)

    for solver in [solve_by_tesseract, solve_by_easyocr]:
        try:
            result = solver(img, options)
            if result:
                candidates.append(result)
        except Exception:
            pass

    try:
        voted = vote_ocr_results(candidates, options)
        if voted:
            candidates.append(voted)
    except Exception:
        pass

    candidates = [c for c in candidates if normalize_option(c[0]) in options]
    if not candidates:
        return None

    by_answer: dict[str, tuple[float, set[str]]] = {}
    for answer, conf, method in candidates:
        answer = normalize_option(answer)
        base_method = str(method).split(":", 1)[0]
        old_conf, methods = by_answer.get(answer, (0.0, set()))
        methods.add(base_method)
        combined = max(old_conf, float(conf)) + min(0.12, 0.04 * (len(methods) - 1))
        by_answer[answer] = (min(0.97, combined), methods)

    ranked = sorted(
        [(ans, conf, "+".join(sorted(methods))) for ans, (conf, methods) in by_answer.items()],
        key=lambda x: x[1],
        reverse=True,
    )
    best_answer, best_conf, best_method = ranked[0]
    detail = _format_candidate_ranking(ranked, limit=5)
    return best_answer, best_conf, best_method, detail



def solve_captcha_image_auto(img, options: list[str]) -> Optional[tuple[str, float, str]]:
    options = [normalize_option(x) for x in options]

    # 1) Best possible if your own captcha generator embeds an answer marker.
    marker_result = decode_plain_answer_marker(img)
    if marker_result:
        answer, conf = marker_result
        if answer in options:
            return answer, min(0.99, max(0.85, conf)), "plain_image_marker"

    # 2) Learned local template matcher. This becomes the most accurate method after
    # you correct/train several captchas with /captcha_answer 1234.
    try:
        learned_result = solve_by_learned_template_match(img, options)
    except Exception as e:
        logging.warning("learned_template_match failed: %s", e)
        learned_result = None
    if learned_result:
        return learned_result

    # 3) Visual matchers are useful for guess/logging, but safe-mode can block auto-click.
    try:
        visual_result = solve_by_visual_option_match(img, options)
    except Exception as e:
        logging.warning("visual_option_match failed: %s", e)
        visual_result = None
    if visual_result:
        return visual_result

    # 2b) OCR-free option-constrained quadrant/template matcher.
    try:
        quadrant_result = solve_by_quadrant_option_match(img, options)
    except Exception as e:
        logging.warning("visual_quadrant_match failed: %s", e)
        quadrant_result = None
    if quadrant_result:
        return quadrant_result

    # 3) OCR engines as fallback.
    results: list[tuple[str, float, str]] = []
    for solver in [solve_by_tesseract, solve_by_easyocr]:
        try:
            result = solver(img, options)
        except Exception as e:
            logging.warning("captcha solver %s failed: %s", getattr(solver, "__name__", solver), e)
            result = None
        if result:
            results.append(result)

    voted = vote_ocr_results(results, options)
    if voted:
        return voted
    if results:
        return max(results, key=lambda x: x[1])
    return None


def _captcha_method_parts(method: str) -> set[str]:
    """Split combined solver method names such as 'ocr_vote+visual_quadrant_match:debug'."""
    raw = str(method or "").strip()
    if not raw:
        return set()
    no_debug = raw.split(":", 1)[0]
    parts = {x.strip() for x in re.split(r"[+,]", no_debug) if x.strip()}
    parts.add(no_debug)
    parts.add(raw)
    return parts


def _captcha_method_allowed(method: str, allowed_methods: set[str]) -> bool:
    if not allowed_methods:
        return False
    allowed = {str(x).strip() for x in allowed_methods if str(x).strip()}
    parts = _captcha_method_parts(method)
    return bool(parts & allowed)


def _captcha_method_is_risky(method: str) -> bool:
    parts = _captcha_method_parts(method)

    # Combined methods such as "ocr_vote+visual_quadrant_match" are not
    # visual-only risky because OCR/learned/plain-marker has confirmed them.
    trusted_parts = {
        "plain_image_marker",
        "learned_template_match",
        "ocr_vote",
        "tesseract_ocr",
        "easyocr_ocr",
    }
    if parts & trusted_parts:
        return False

    risky_methods = {
        x.strip()
        for x in os.getenv(
            "CAPTCHA_RISKY_AUTO_BLOCK_METHODS",
            "visual_option_match,visual_quadrant_match",
        ).split(",")
        if x.strip()
    }
    if not risky_methods:
        return False
    return bool(parts & risky_methods)


async def _try_auto_click_captcha_guess(
    app: Client,
    session_key: str,
    m,
    answer: str,
    confidence: float,
    method: str,
    options: list[str],
    label: str = "best_guess",
) -> bool:
    """Auto-click a captcha guess if env rules allow it."""
    auto_enabled = CONFIG.get("captcha_auto_approve", False)
    if not auto_enabled:
        return False

    auto_methods = CONFIG.get("captcha_auto_approve_methods", set())
    if not _captcha_method_allowed(method, auto_methods):
        await send_log(
            "🧩 <b>Captcha best guess not clicked.</b>\n"
            f"Session: <code>{html.escape(session_key)}</code>\n"
            f"Answer: <code>{html.escape(answer)}</code> (<code>{confidence * 100:.1f}%</code>)\n"
            f"Method: <code>{html.escape(method)}</code>\n"
            f"Reason: <code>method not allowed by CAPTCHA_AUTO_APPROVE_METHODS</code>\n"
            f"Options: <code>{html.escape(' | '.join(options))}</code>\n"
            "Action: <code>not clicked</code>",
            parse_html=True,
            app=app,
        )
        return False

    allow_risky_visual_auto = getenv_bool("CAPTCHA_ALLOW_RISKY_VISUAL_AUTO", False)
    if _captcha_method_is_risky(method) and not allow_risky_visual_auto:
        await send_log(
            "🛡️ <b>Captcha auto-click blocked by safe mode.</b>\n"
            f"Session: <code>{html.escape(session_key)}</code>\n"
            f"Detected: <code>{html.escape(answer)}</code> (<code>{confidence * 100:.1f}%</code>)\n"
            f"Method: <code>{html.escape(method)}</code>\n"
            f"Reason: <code>visual/risky method blocked. Set CAPTCHA_ALLOW_RISKY_VISUAL_AUTO=true to allow.</code>\n"
            f"Options: <code>{html.escape(' | '.join(options))}</code>\n"
            "Action: <code>approval needed</code>",
            parse_html=True,
            app=app,
        )
        return False

    clicked = await click_button_by_text_pyro(m, answer)
    if clicked:
        await send_log(
            "✅ <b>Captcha auto-clicked.</b>\n"
            f"Session: <code>{html.escape(session_key)}</code>\n"
            f"Answer: <code>{html.escape(answer)}</code>\n"
            f"Confidence: <code>{confidence * 100:.1f}%</code>\n"
            f"Method: <code>{html.escape(method)}</code>\n"
            f"Source: <code>{html.escape(label)}</code>\n"
            f"Options: <code>{html.escape(' | '.join(options))}</code>",
            parse_html=True,
            app=app,
        )
        return True

    await send_log(
        "❌ <b>Captcha auto-click failed.</b>\n"
        f"Session: <code>{html.escape(session_key)}</code>\n"
        f"Answer: <code>{html.escape(answer)}</code>\n"
        f"Method: <code>{html.escape(method)}</code>\n"
        f"Options: <code>{html.escape(' | '.join(options))}</code>",
        parse_html=True,
        app=app,
    )
    return False


async def captcha_cleanup_expired() -> None:
    timeout = CONFIG.get("captcha_approval_timeout", 120)
    now = time.time()
    expired: list[int] = []

    async with captcha_lock:
        for rid, item in pending_captchas.items():
            if now - float(item.get("created_at", now)) > timeout:
                expired.append(rid)

        for rid in expired:
            item = pending_captchas.pop(rid, None)
            if item:
                captcha_message_to_request.pop(
                    (item.get("session_key"), item.get("chat_id"), item.get("message_id")),
                    None,
                )

    for rid in expired:
        await send_log(f"⌛ Captcha approval expired. Request ID: <code>{rid}</code>", parse_html=True)


async def captcha_cleanup_loop() -> None:
    while True:
        try:
            await captcha_cleanup_expired()
        except Exception as e:
            logging.warning("captcha_cleanup_loop failed: %s", e)
        await asyncio.sleep(10)


def make_captcha_request_id(session_key: str, chat_id: int, message_id: int) -> int:
    prefix = 1 if session_key == "a" else 2
    return int(f"{prefix}{abs(chat_id) % 100000}{message_id}")


async def add_pending_captcha(
    app: Client,
    session_key: str,
    m,
    options: list[str],
    answer: str,
    confidence: float,
    method: str,
    image_path: str = "",
) -> int:
    chat_id = int(m.chat.id)
    message_id = int(m.id)
    req_id = make_captcha_request_id(session_key, chat_id, message_id)
    key = (session_key, chat_id, message_id)

    async with captcha_lock:
        if key in captcha_message_to_request:
            return captcha_message_to_request[key]

        item = {
            "request_id": req_id,
            "session_key": session_key,
            "chat_id": chat_id,
            "message_id": message_id,
            "options": options,
            "detected_answer": normalize_option(answer),
            "confidence": float(confidence),
            "method": method,
            "image_path": image_path,
            "created_at": time.time(),
        }

        pending_captchas[req_id] = item
        captcha_message_to_request[key] = req_id

    try:
        await app.forward_messages(CONFIG["log_group_id"], chat_id, message_id)
    except Exception:
        pass

    await send_log(
        "🧩 <b>Captcha answer detected. Approval needed.</b>\n"
        f"Request ID: <code>{req_id}</code>\n"
        f"Session: <code>{html.escape(session_key)}</code>\n"
        f"Detected: <code>{html.escape(normalize_option(answer))}</code>\n"
        f"Confidence: <code>{confidence * 100:.1f}%</code>\n"
        f"Method: <code>{html.escape(method)}</code>\n"
        f"Options: <code>{html.escape(' | '.join(options))}</code>\n\n"
        "Approve: <code>/approve</code> or <code>/approve_id REQUEST_ID</code>\n"
        "Reject: <code>/reject</code> or <code>/reject REQUEST_ID</code>",
        parse_html=True,
        app=app,
    )

    return req_id


async def click_captcha_item(app: Client, item: dict[str, Any]) -> bool:
    try:
        msg = await app.get_messages(int(item["chat_id"]), int(item["message_id"]))
        if not msg:
            return False
        return await click_button_by_text_pyro(msg, str(item["detected_answer"]))
    except Exception as e:
        logging.warning("captcha click failed: %s", e)
        return False


async def approve_captcha_request(m, request_id: Optional[int] = None) -> None:
    async with captcha_lock:
        if not pending_captchas:
            await m.reply("No pending captcha approval.")
            return

        if request_id is None:
            request_id = max(
                pending_captchas.keys(),
                key=lambda rid: pending_captchas[rid].get("created_at", 0),
            )

        item = pending_captchas.get(request_id)
        if not item:
            await m.reply(f"❌ Request ID not found: <code>{request_id}</code>", parse_mode=ParseMode.HTML)
            return

    app = app_a if item.get("session_key") == "a" else app_b
    if app is None:
        await m.reply("❌ Client session not available.")
        return

    clicked = await click_captcha_item(app, item)
    if not clicked:
        await m.reply(
            "❌ Matching button not found or click failed.\n"
            f"Answer: <code>{html.escape(str(item.get('detected_answer')))}</code>",
            parse_mode=ParseMode.HTML,
        )
        return

    learned = False
    image_path = item.get("image_path") or ""
    if image_path and os.path.exists(image_path) and captcha_cv_ready():
        img = cv2.imread(image_path)
        learned = await save_learned_captcha_templates_from_image(
            img,
            str(item.get("detected_answer")),
            str(item.get("session_key")),
            int(item.get("chat_id")),
            int(item.get("message_id")),
        )

    async with captcha_lock:
        pending_captchas.pop(int(item["request_id"]), None)
        captcha_message_to_request.pop(
            (item.get("session_key"), item.get("chat_id"), item.get("message_id")),
            None,
        )

    await m.reply(
        "✅ Captcha approved and clicked.\n"
        f"Learned: <code>{learned}</code>\n"
        f"Request ID: <code>{item['request_id']}</code>\n"
        f"Answer: <code>{html.escape(str(item.get('detected_answer')))}</code>\n"
        f"Method: <code>{html.escape(str(item.get('method')))}</code>",
        parse_mode=ParseMode.HTML,
    )


async def reject_captcha_request(m, request_id: Optional[int] = None) -> None:
    async with captcha_lock:
        if not pending_captchas:
            await m.reply("No pending captcha approval.")
            return

        if request_id is None:
            request_id = max(
                pending_captchas.keys(),
                key=lambda rid: pending_captchas[rid].get("created_at", 0),
            )

        item = pending_captchas.pop(request_id, None)
        if not item:
            await m.reply(f"Request ID not found: <code>{request_id}</code>", parse_mode=ParseMode.HTML)
            return

        captcha_message_to_request.pop(
            (item.get("session_key"), item.get("chat_id"), item.get("message_id")),
            None,
        )

    await m.reply(
        "❌ Captcha request rejected.\n"
        f"Request ID: <code>{request_id}</code>\n"
        f"Detected: <code>{html.escape(str(item.get('detected_answer')))}</code>",
        parse_mode=ParseMode.HTML,
    )


async def send_captcha_pending(m) -> None:
    async with captcha_lock:
        items = list(pending_captchas.values())

    if not items:
        await m.reply("No pending captcha approval.")
        return

    now = time.time()
    lines = ["🧩 <b>Pending captcha approvals</b>"]
    for item in sorted(items, key=lambda x: x.get("created_at", 0)):
        age = int(now - float(item.get("created_at", now)))
        lines.append(
            f"• ID <code>{item.get('request_id')}</code> | "
            f"session <code>{html.escape(str(item.get('session_key')))}</code> | "
            f"answer <code>{html.escape(str(item.get('detected_answer')))}</code> | "
            f"conf <code>{float(item.get('confidence', 0.0)):.2f}</code> | "
            f"method <code>{html.escape(str(item.get('method')))}</code> | age {age}s"
        )

    lines.append(
        "\nApprove latest: <code>/approve</code>\n"
        "Approve by ID: <code>/approve_id ID</code>\n"
        "Reject: <code>/reject</code>"
    )
    await m.reply("\n".join(lines), parse_mode=ParseMode.HTML)



def _captcha_debug_image_path(session_key: str, chat_id: int, message_id: int) -> str:
    safe_chat = str(chat_id).replace("-", "m")
    return os.path.join(DATA_DIR, f"captcha_{session_key}_{safe_chat}_{message_id}.jpg")


async def remember_recent_captcha(session_key: str, m, options: list[str], img) -> Optional[str]:
    if not captcha_cv_ready() or img is None:
        return None
    chat_id = int(m.chat.id)
    message_id = int(m.id)
    image_path = _captcha_debug_image_path(session_key, chat_id, message_id)
    try:
        cv2.imwrite(image_path, img)
    except Exception:
        image_path = ""
    key = (session_key, chat_id, message_id)
    async with captcha_lock:
        captcha_recent_items[key] = {
            "session_key": session_key,
            "chat_id": chat_id,
            "message_id": message_id,
            "options": list(options),
            "image_path": image_path,
            "created_at": time.time(),
        }
        if len(captcha_recent_items) > 100:
            oldest = sorted(captcha_recent_items.items(), key=lambda kv: kv[1].get("created_at", 0))[:-100]
            for old_key, _ in oldest:
                captcha_recent_items.pop(old_key, None)
    return image_path


async def get_latest_recent_captcha(session_key: Optional[str] = None) -> Optional[dict[str, Any]]:
    async with captcha_lock:
        items = [dict(v) for v in captcha_recent_items.values()]
    now = time.time()
    items = [x for x in items if now - float(x.get("created_at", now)) <= 300]
    if session_key:
        items = [x for x in items if x.get("session_key") == session_key]
    if not items:
        return None
    items.sort(key=lambda x: x.get("created_at", 0), reverse=True)
    return items[0]


async def handle_captcha_photo_caption_learning(app: Client, m, answer: str) -> bool:
    """
    Manual learning from an owner-sent photo with caption like:
        /captcha_answer 1351

    This is TRAIN-ONLY because the uploaded photo is not the original captcha
    message with buttons. It improves learned_template_match for future captchas.
    """
    answer = normalize_option(answer)
    if not re.fullmatch(r"\d{4}", answer):
        await m.reply("❌ Usage: <code>/captcha_answer 1234</code>", parse_mode=ParseMode.HTML)
        return True

    if not getattr(m, "photo", None):
        return False

    if not captcha_cv_ready():
        await m.reply(
            "❌ OpenCV/Numpy မရှိသေးပါ။ requirements ထဲမှာ opencv-python-headless + numpy install လိုပါတယ်။"
        )
        return True

    img = await download_pyro_message_media_as_cv2(app, m)
    if img is None:
        await m.reply("❌ Photo ကို download/decode မလုပ်နိုင်ပါ။")
        return True

    learned = await save_learned_captcha_templates_from_image(
        img,
        answer,
        "manual_photo",
        int(m.chat.id) if m.chat else 0,
        int(m.id),
    )

    total, counts = await _count_captcha_templates()
    if learned:
        await m.reply(
            "✅ Captcha photo learned successfully.\n"
            f"Answer: <code>{html.escape(answer)}</code>\n"
            f"Templates: <code>{total}</code>\n"
            f"Counts: <code>{html.escape(', '.join(f'{k}:{v}' for k, v in sorted(counts.items())) or 'none')}</code>\n\n"
            "မှတ်ချက်: Photo+caption learning က train-only ပါ။ လက်ရှိ captcha button ကိုနှိပ်တာမလုပ်ပါဘူး။",
            parse_mode=ParseMode.HTML,
        )
        await send_log(
            "🧠 <b>Captcha manual photo learned</b>\n"
            f"Answer: <code>{html.escape(answer)}</code>\n"
            f"Templates: <code>{total}</code>\n"
            f"Source: <code>owner_photo_caption</code>",
            parse_html=True,
            app=app,
        )
    else:
        await m.reply(
            "⚠️ Captcha photo learning failed.\n"
            f"Answer: <code>{html.escape(answer)}</code>\n"
            "Reason: 4 digits ကို image ထဲကနေ ခွဲမထုတ်နိုင်သေးပါ။\n\n"
            "အကောင်းဆုံးရလဒ်အတွက် captcha number ပုံကို crop လုပ်ပြီး ပို့ပါ။ Telegram UI/screenshot တစ်ခုလုံးမပို့ပါနဲ့။",
            parse_mode=ParseMode.HTML,
        )

    return True


async def handle_captcha_manual_answer(app_or_message, m_or_answer=None, answer_value: Optional[str] = None) -> None:
    """
    Supports both call styles:
      old: handle_captcha_manual_answer(m, answer)
      new: handle_captcha_manual_answer(app, m, answer)

    If owner sends photo + caption /captcha_answer 1234, learn from that photo.
    Otherwise, use latest recent captcha: click answer + learn from saved original captcha image.
    """
    if answer_value is None:
        app = app_a or app_b
        m = app_or_message
        answer = str(m_or_answer or "")
    else:
        app = app_or_message
        m = m_or_answer
        answer = str(answer_value or "")

    if app is None:
        await m.reply("❌ Client session not available.")
        return

    # New path: owner sends captcha photo with caption /captcha_answer 1234
    handled_photo = await handle_captcha_photo_caption_learning(app, m, answer)
    if handled_photo:
        return

    answer = normalize_option(answer)
    if not re.fullmatch(r"\d{4}", answer):
        await m.reply("❌ Usage: <code>/captcha_answer 1234</code>", parse_mode=ParseMode.HTML)
        return
    item = await get_latest_recent_captcha()
    if not item:
        await m.reply("❌ No recent captcha image found. Try again right after captcha appears.")
        return
    if answer not in [normalize_option(x) for x in item.get("options", [])]:
        await m.reply(
            "❌ Answer is not in current button options.\n"
            f"Answer: <code>{html.escape(answer)}</code>\n"
            f"Options: <code>{html.escape(' | '.join(item.get('options', [])))}</code>",
            parse_mode=ParseMode.HTML,
        )
        return
    app = app_a if item.get("session_key") == "a" else app_b
    if app is None:
        await m.reply("❌ Client session not available.")
        return
    clicked = False
    try:
        msg = await app.get_messages(int(item["chat_id"]), int(item["message_id"]))
        clicked = await click_button_by_text_pyro(msg, answer)
    except Exception as e:
        logging.warning("manual captcha answer click failed: %s", e)
    learned = False
    image_path = item.get("image_path") or ""
    if image_path and os.path.exists(image_path) and captcha_cv_ready():
        img = cv2.imread(image_path)
        learned = await save_learned_captcha_templates_from_image(
            img,
            answer,
            str(item.get("session_key")),
            int(item.get("chat_id")),
            int(item.get("message_id")),
        )
    total, counts = await _count_captcha_templates()
    await m.reply(
        f"{'✅' if clicked else '⚠️'} Captcha answer handled.\n"
        f"Clicked: <code>{clicked}</code>\n"
        f"Learned: <code>{learned}</code>\n"
        f"Answer: <code>{html.escape(answer)}</code>\n"
        f"Templates: <code>{total}</code>\n"
        f"Counts: <code>{html.escape(', '.join(f'{k}:{v}' for k, v in sorted(counts.items())) or 'none')}</code>",
        parse_mode=ParseMode.HTML,
    )


async def send_captcha_learn_status(m) -> None:
    total, counts = await _count_captcha_templates()
    min_templates = int(CONFIG.get("captcha_learning_min_templates", 3))
    lines = [
        "🧠 <b>Captcha Learning Status</b>",
        f"Enabled: {'✅ ON' if CONFIG.get('captcha_learning_enabled', True) else '❌ OFF'}",
        f"Total templates: <code>{total}</code>",
        f"Min templates per digit: <code>{min_templates}</code>",
        "Counts:",
    ]
    for d in map(str, range(10)):
        v = counts.get(d, 0)
        lines.append(f"• <code>{d}</code>: <code>{v}</code> {'✅' if v >= min_templates else '⚠️'}")
    lines.append("\nManual train/click latest: <code>/captcha_answer 1234</code>")
    lines.append("Photo train only: send captcha photo with caption <code>/captcha_answer 1234</code>")
    await m.reply("\n".join(lines), parse_mode=ParseMode.HTML)

async def handle_captcha_solver(app: Client, session_key: str, m) -> None:
    if not CONFIG.get("captcha_solver_enabled"):
        return

    if session_key not in CONFIG.get("captcha_solver_sessions", {"a"}):
        return

    if not looks_like_captcha_message(m):
        return

    key = (session_key, int(m.chat.id), int(m.id))
    async with captcha_lock:
        if key in processed_captcha_messages:
            return

        processed_captcha_messages.add(key)
        if len(processed_captcha_messages) > 3000:
            processed_captcha_messages.clear()

    options = extract_numeric_buttons_pyro(m)
    if not options:
        return

    if not captcha_cv_ready():
        await send_log(
            "🧩 Captcha solver skipped: install <code>opencv-python-headless numpy</code>.",
            parse_html=True,
            app=app,
        )
        return

    img = await download_pyro_message_media_as_cv2(app, m)
    if img is None:
        await send_log("🧩 Captcha image download/decode failed.", parse_html=True, app=app)
        return

    image_path = await remember_recent_captcha(session_key, m, options, img)

    result = solve_captcha_image_auto(img, options)

    # Weak visual-only direct results are moved into the best-guess consensus flow.
    # This avoids clicking low-confidence visual guesses while still allowing fast
    # auto-click when OCR vote / learned template confirms the answer.
    if result:
        _ans0, _conf0, _method0 = result
        visual_direct_min = getenv_float("CAPTCHA_VISUAL_DIRECT_MIN_CONFIDENCE", 0.70)
        if _captcha_method_is_risky(str(_method0)) and float(_conf0) < visual_direct_min:
            logging.warning(
                "weak visual direct result moved to best-guess flow | answer=%s conf=%.3f method=%s",
                _ans0, float(_conf0), _method0,
            )
            result = None

    if not result:
        best_guess = get_captcha_best_guess(img, options)
        if best_guess:
            guess_answer, guess_conf, guess_method, guess_detail = best_guess

            # Allow best-guess auto click when confidence and method rules pass.
            best_guess_auto = getenv_bool("CAPTCHA_AUTO_CLICK_BEST_GUESS", True)
            best_guess_min = getenv_float(
                "CAPTCHA_BEST_GUESS_MIN_CONFIDENCE",
                CONFIG.get("captcha_auto_min_confidence", 0.75),
            )
            if best_guess_auto and guess_conf >= best_guess_min:
                clicked = await _try_auto_click_captcha_guess(
                    app,
                    session_key,
                    m,
                    normalize_option(guess_answer),
                    float(guess_conf),
                    str(guess_method),
                    options,
                    label="best_guess",
                )
                if clicked:
                    return

            if CONFIG.get("captcha_log_no_answer", True):
                guess_text = _format_captcha_guess(guess_answer, guess_conf, guess_method, guess_detail)
                await send_log(
                    "🧩 <b>Captcha detected but no confident answer found.</b>\n"
                    f"Session: <code>{html.escape(session_key)}</code>\n"
                    f"Options: <code>{html.escape(' | '.join(options))}</code>\n"
                    f"{guess_text}\n"
                    f"Best guess auto: <code>{'ON' if best_guess_auto else 'OFF'}</code>\n"
                    f"Best guess min: <code>{best_guess_min * 100:.1f}%</code>\n"
                    "Action: <code>not clicked</code>",
                    parse_html=True,
                    app=app,
                )
        else:
            if CONFIG.get("captcha_log_no_answer", True):
                await send_log(
                    "🧩 <b>Captcha detected but no confident answer found.</b>\n"
                    f"Session: <code>{html.escape(session_key)}</code>\n"
                    f"Options: <code>{html.escape(' | '.join(options))}</code>\n"
                    "Best guess: <code>None</code>\n"
                    "Action: <code>not clicked</code>",
                    parse_html=True,
                    app=app,
                )
        return

    answer, confidence, method = result
    min_conf = CONFIG.get("captcha_min_confidence", 0.60)
    if confidence < min_conf:
        best_guess = get_captcha_best_guess(img, options)
        guess_text = ""
        if best_guess:
            guess_answer, guess_conf, guess_method, guess_detail = best_guess
            guess_text = "\n" + _format_captcha_guess(guess_answer, guess_conf, guess_method, guess_detail)
        await send_log(
            "🧩 <b>Captcha answer found but confidence too low.</b>\n"
            f"Answer: <code>{html.escape(answer)}</code> (<code>{confidence * 100:.1f}%</code>)\n"
            f"Required: <code>{min_conf * 100:.1f}%</code>\n"
            f"Method: <code>{html.escape(method)}</code>\n"
            f"Options: <code>{html.escape(' | '.join(options))}</code>"
            f"{guess_text}\n"
            "Action: <code>not clicked</code>",
            parse_html=True,
            app=app,
        )
        return

    auto_methods = CONFIG.get("captcha_auto_approve_methods", set())
    auto_enabled = CONFIG.get("captcha_auto_approve", False)
    auto_min = CONFIG.get("captcha_auto_min_confidence", 0.75)
    method_base = method.split(":", 1)[0]
    can_auto = auto_enabled and confidence >= auto_min and _captcha_method_allowed(method, auto_methods)

    # Safety guard: visual-only methods can be wrong when colored lines cross digits.
    # They are useful for best-guess logging, but should not auto-click unless explicitly allowed.
    risky_visual_methods = {
        x.strip()
        for x in os.getenv(
            "CAPTCHA_RISKY_AUTO_BLOCK_METHODS",
            "visual_option_match,visual_quadrant_match",
        ).split(",")
        if x.strip()
    }
    allow_risky_visual_auto = getenv_bool("CAPTCHA_ALLOW_RISKY_VISUAL_AUTO", False)

    if _captcha_method_is_risky(method) and not allow_risky_visual_auto:
        if can_auto:
            await send_log(
                "🛡️ <b>Captcha auto-click blocked by safe mode.</b>\n"
                f"Session: <code>{html.escape(session_key)}</code>\n"
                f"Detected: <code>{html.escape(answer)}</code> (<code>{confidence * 100:.1f}%</code>)\n"
                f"Method: <code>{html.escape(method)}</code>\n"
                f"Reason: <code>visual-only methods are not trusted for auto-click</code>\n"
                f"Options: <code>{html.escape(' | '.join(options))}</code>\n"
                "Action: <code>approval needed</code>",
                parse_html=True,
                app=app,
            )
        can_auto = False

    if can_auto:
        clicked = await click_button_by_text_pyro(m, answer)
        if clicked:
            await send_log(
                "✅ <b>Captcha auto-clicked.</b>\n"
                f"Session: <code>{html.escape(session_key)}</code>\n"
                f"Answer: <code>{html.escape(answer)}</code>\n"
                f"Confidence: <code>{confidence * 100:.1f}%</code>\n"
                f"Method: <code>{html.escape(method)}</code>\n"
                f"Options: <code>{html.escape(' | '.join(options))}</code>",
                parse_html=True,
                app=app,
            )
            return

        await send_log("❌ Captcha auto-click failed; fallback to approval.", parse_html=True, app=app)

    await add_pending_captcha(app, session_key, m, options, answer, confidence, method, image_path or "")


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
        f"Auto Catch Sessions: {html.escape(','.join(sorted(CONFIG.get('auto_catch_sessions', []))))}\n"
        f"Captcha Solver: {'✅ ON' if CONFIG.get('captcha_solver_enabled') else '❌ OFF'} | "
        f"Captcha Auto: {'✅ ON' if CONFIG.get('captcha_auto_approve') else '❌ OFF'}\n"
        f"Direct DB Catch: {'✅ ON' if CONFIG.get('direct_db_catch_enabled') else '❌ OFF'} | "
        f"Sessions: {html.escape(','.join(sorted(CONFIG.get('direct_db_sessions', []))))}"
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
        "<b>Captcha Solver:</b>\n"
        "• <code>/captcha_auto_on</code> - detected answer ကို auto click\n"
        "• <code>/captcha_auto_off</code> - approval mode ပြန်သုံး\n"
        "• <code>/captcha_auto_status</code> - captcha solver status\n"
        "• <code>/captcha_pending</code> or <code>/pending</code> - pending captcha list\n"
        "• <code>/captcha_answer 1234</code> - latest captcha click + learn\n"
        "• photo + caption <code>/captcha_answer 1234</code> - train from photo only\n"
        "• <code>/captcha_learn_status</code> - learned template count\n"
        "• <code>/approve</code> or <code>/approve_id ID</code> - approve and click\n"
        "• <code>/reject</code> or <code>/reject ID</code> - reject captcha\n\n"
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

        text = (m.text or m.caption or "").strip()
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

        if cmd == "/captcha_auto_on":
            CONFIG["captcha_auto_approve"] = True
            await m.reply("✅ Captcha auto approve is now ON.")
            return

        if cmd == "/captcha_auto_off":
            CONFIG["captcha_auto_approve"] = False
            await m.reply("❌ Captcha auto approve is now OFF. Bot will ask approval before clicking.")
            return

        if cmd == "/captcha_auto_status":
            async with captcha_lock:
                pending_count = len(pending_captchas)

            await m.reply(
                "🧩 <b>Captcha Solver Status</b>\n"
                f"Enabled: {'✅ ON' if CONFIG.get('captcha_solver_enabled') else '❌ OFF'}\n"
                f"Auto approve: {'✅ ON' if CONFIG.get('captcha_auto_approve') else '❌ OFF'}\n"
                f"Solver sessions: <code>{html.escape(','.join(sorted(CONFIG.get('captcha_solver_sessions', []))))}</code>\n"
                f"Target groups: <code>{html.escape(format_id_list(CONFIG.get('captcha_target_groups', set())))}</code>\n"
                f"Captcha bot id: <code>{html.escape(str(CONFIG.get('captcha_bot_id')))}</code>\n"
                f"Min confidence: <code>{CONFIG.get('captcha_min_confidence'):.2f}</code>\n"
                f"Auto min confidence: <code>{CONFIG.get('captcha_auto_min_confidence'):.2f}</code>\n"
                f"Auto methods: <code>{html.escape(','.join(sorted(CONFIG.get('captcha_auto_approve_methods', []))))}</code>\n"
                f"Tesseract: {'✅' if CONFIG.get('enable_tesseract_ocr') else '❌'} | "
                f"EasyOCR: {'✅' if CONFIG.get('enable_easyocr') else '❌'}\n"
                f"OpenCV ready: {'✅' if captcha_cv_ready() else '❌'}\n"
                f"Learning: {'✅ ON' if CONFIG.get('captcha_learning_enabled', True) else '❌ OFF'}\n"
                f"Templates: <code>{(await _count_captcha_templates())[0]}</code>\n"
                f"Pending: <code>{pending_count}</code>",
                parse_mode=ParseMode.HTML,
            )
            return

        if cmd in {"/captcha_pending", "/pending"}:
            await send_captcha_pending(m)
            return

        if cmd in {"/captcha_answer", "/captcha_correct", "/answer", "/captcha_train"}:
            parts = text.split()
            if len(parts) < 2:
                await m.reply("❌ Usage: <code>/captcha_answer 1234</code>", parse_mode=ParseMode.HTML)
                return
            await handle_captcha_manual_answer(_, m, parts[1])
            return

        if cmd in {"/captcha_learn_status", "/captcha_learning_status"}:
            await send_captcha_learn_status(m)
            return

        if cmd == "/approve":
            await approve_captcha_request(m)
            return

        if cmd == "/approve_id":
            parts = text.split()
            if len(parts) < 2 or not parts[1].isdigit():
                await m.reply("❌ Usage: <code>/approve_id REQUEST_ID</code>", parse_mode=ParseMode.HTML)
                return
            await approve_captcha_request(m, int(parts[1]))
            return

        if cmd == "/reject":
            parts = text.split()
            request_id = int(parts[1]) if len(parts) >= 2 and parts[1].isdigit() else None
            await reject_captcha_request(m, request_id)
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


async def warmup_captcha_engines() -> None:
    """Preload captcha template/OCR engines in background for the first captcha."""
    if not CONFIG.get("captcha_solver_enabled"):
        return
    try:
        if captcha_cv_ready():
            await asyncio.to_thread(_get_digit_template_cache)
            await asyncio.to_thread(_load_learned_digit_templates_sync)
        if CONFIG.get("enable_easyocr", False):
            await asyncio.to_thread(_get_easyocr_reader)
        if getenv_bool("CAPTCHA_WARMUP_LOG", False):
            await send_log(
                "🔥 <b>Captcha engines warmed up.</b>\n"
                f"OpenCV: {'✅' if captcha_cv_ready() else '❌'} | "
                f"Tesseract: {'✅' if CONFIG.get('enable_tesseract_ocr') else '❌'} | "
                f"EasyOCR: {'✅' if CONFIG.get('enable_easyocr') else '❌'}",
                parse_html=True,
                app=app_a,
            )
    except Exception as e:
        logging.warning("captcha engine warmup failed: %s", e)


async def handle_general_message(app: Client, session_key: str, m) -> None:
    try:
        # Captcha has only 60 seconds. Solve/click first, then do logs/mentions.
        await handle_captcha_solver(app, session_key, m)
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
    owner_filter = filters.user(list(CONFIG["owner_ids"]))

    # Broad early handlers are intentional.
    # Some bot DMs are ChatType.BOT instead of ChatType.PRIVATE, so filters.private can miss them.
    # handle_responder_dm() self-filters by chat type, sender, /catch text, and dedupe.
    @app_a.on_message(group=-2)
    async def responder_dm_a(_, m):
        await handle_responder_dm(app_a, "a", m)

    @app_b.on_message(group=-2)
    async def responder_dm_b(_, m):
        await handle_responder_dm(app_b, "b", m)

    # Owner commands can be text OR photo+caption, e.g. /captcha_answer 1351.
    @app_a.on_message(owner_filter, group=0)
    async def commands_a(_, m):
        await handle_owner_command(_, m)

    @app_a.on_message(group=1)
    async def general_a(_, m):
        await handle_general_message(app_a, "a", m)

    @app_b.on_message(group=1)
    async def general_b(_, m):
        await handle_general_message(app_b, "b", m)

    @app_a.on_edited_message(group=1)
    async def edited_a(_, m):
        await handle_edited_message(app_a, "a", m)

    @app_b.on_edited_message(group=1)
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

    if direct_mongo_client is not None:
        direct_mongo_client.close()


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
        f"Captcha Solver: {'✅ ON' if CONFIG.get('captcha_solver_enabled') else '❌ OFF'} | Auto: {'✅ ON' if CONFIG.get('captcha_auto_approve') else '❌ OFF'}\n"
        f"Direct DB Catch: {'✅ ON' if CONFIG.get('direct_db_catch_enabled') else '❌ OFF'} | Sessions: <code>{html.escape(','.join(sorted(CONFIG.get('direct_db_sessions', []))))}</code>\n"
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

    # Warm up Pyrogram peer cache so LOG_GROUP_ID works with in_memory string sessions.
    await warmup_peer_cache(app_a)

    await init_direct_db()

    logging.warning(
        "Started successfully | session_a_id=%s | session_b_id=%s | groups=%s | auto_forward=%s",
        session_a_id,
        session_b_id,
        format_id_list(CONFIG["group_ids"]),
        CONFIG.get("auto_forward_enabled"),
    )

    await send_startup_summary()

    captcha_cleanup_task = asyncio.create_task(captcha_cleanup_loop())
    captcha_warmup_task = asyncio.create_task(warmup_captcha_engines())

    try:
        await idle()
    finally:
        stop_active_timer()
        if 'captcha_cleanup_task' in locals() and captcha_cleanup_task and not captcha_cleanup_task.done():
            captcha_cleanup_task.cancel()
        if 'captcha_warmup_task' in locals() and captcha_warmup_task and not captcha_warmup_task.done():
            captcha_warmup_task.cancel()
        await shutdown_clients()


if __name__ == "__main__":
    asyncio.run(main())
