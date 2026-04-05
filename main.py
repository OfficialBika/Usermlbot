import asyncio
import json
import logging
import os
import random
from typing import Optional, List

from pyrogram import Client, filters, idle
from pyrogram.enums import ChatType, ChatAction
from pyrogram.errors import FloodWait

# ================= CONFIG =================

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
CONFIG_FILE = os.path.join(BASE_DIR, "config.json")
LOCALES_DIR = os.path.join(BASE_DIR, "locales")

SESSA_FILE = os.path.join(LOCALES_DIR, "sessa.txt")
SESSB_FILE = os.path.join(LOCALES_DIR, "sessb.txt")

EMOJIS = ["😂","😅","😆","😎","🔥","🙂","🤭","😁"]

# ================= GLOBAL =================

CONFIG = {}
app_a: Optional[Client] = None
app_b: Optional[Client] = None

last_sender = None

session_a_id = None
session_b_id = None

sessa_lines: List[str] = []
sessb_lines: List[str] = []

enabled = False

# ================= LOAD =================

def load_config():
    with open(CONFIG_FILE, "r") as f:
        return json.load(f)

def load_lines(path):
    try:
        with open(path, "r", encoding="utf-8") as f:
            return [x.strip() for x in f if x.strip()]
    except:
        return []

# ================= CORE =================

async def ensure_ids():
    global session_a_id, session_b_id
    if not session_a_id:
        session_a_id = (await app_a.get_me()).id
    if not session_b_id:
        session_b_id = (await app_b.get_me()).id


def get_text(which):
    if which == "a":
        text = random.choice(sessa_lines)
    else:
        text = random.choice(sessb_lines)

    # emoji chance
    if random.random() < 0.5:
        text += " " + random.choice(EMOJIS)

    # small chance send only emoji
    if random.random() < 0.1:
        text = random.choice(EMOJIS)

    return text


async def send_human(app, chat_id, reply_to, text):
    try:
        await asyncio.sleep(random.uniform(CONFIG["min_reply_delay"], CONFIG["max_reply_delay"]))
        await app.send_chat_action(chat_id, ChatAction.TYPING)
        await asyncio.sleep(random.uniform(2, 5))

        if random.random() < 0.8 or not reply_to:
            msg = await app.send_message(chat_id, text)
        else:
            msg = await app.send_message(chat_id, text, reply_to_message_id=reply_to)

        return msg

    except FloodWait as e:
        await asyncio.sleep(e.value)
        return None
    except Exception as e:
        print("send_human error:", e)
        return None
# ================= HANDLERS =================

def register():
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

    @app_b.on_message(filters.chat(CONFIG["group_id"]) & filters.incoming & filters.text)
    async def watch_b(_, m):
        if not enabled:
            return
        if not m.from_user:
            return

        await ensure_ids()
        print("watch_b triggered:", m.from_user.id, m.text)

        if m.from_user.id == session_a_id:
            print("A sent -> B reply")
            msg_b = await send_human(app_b, CONFIG["group_id"], m.id, get_text("b"))

            if msg_b:
                print("B sent -> A reply")
                await send_human(app_a, CONFIG["group_id"], msg_b.id, get_text("a"))
# ================= START =================

async def main():
    global CONFIG, app_a, app_b, sessa_lines, sessb_lines

    CONFIG = load_config()

    sessa_lines = load_lines(SESSA_FILE)
    sessb_lines = load_lines(SESSB_FILE)

    app_a = Client(CONFIG["session_a"], CONFIG["api_id"], CONFIG["api_hash"])
    app_b = Client(CONFIG["session_b"], CONFIG["api_id"], CONFIG["api_hash"])

    await app_a.start()
    await app_b.start()

    async for _ in app_a.get_dialogs():
        pass
    async for _ in app_b.get_dialogs():
        pass

    await ensure_ids()
    print("Session A ID:", session_a_id)
    print("Session B ID:", session_b_id)

    register()

    print("Bot Running...")

    await idle()

    await app_a.stop()
    await app_b.stop()


if __name__ == "__main__":
    asyncio.run(main())
