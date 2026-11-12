import asyncio
import os
import sqlite3
import threading
import unittest
from unittest.mock import patch

import main


class RuntimeBehaviorTests(unittest.TestCase):
    def test_load_config_preserves_safe_feature_defaults_and_session_boundaries(self):
        environment = {
            "API_ID": "123456",
            "API_HASH": "test-api-hash",
            "SESSION_A_STRING": "session_a_test=",
            "SESSION_B_STRING": "session_b_test=",
            "OWNER_IDS": "12345",
            "GROUP_IDS": "-1001234567890",
        }
        with patch.dict(os.environ, environment, clear=True):
            config = main.load_config()

        self.assertFalse(config["auto_forward_enabled"])
        self.assertFalse(config["direct_db_catch_enabled"])
        self.assertFalse(config["captcha_solver_enabled"])
        self.assertFalse(config["captcha_auto_approve"])
        self.assertEqual(config["human_chat_sessions"], {"a", "b", "c", "d", "e", "f", "g", "h"})
        self.assertEqual(config["auto_catch_sessions"], {"a", "b", "c", "d", "e", "f", "g", "h"})
        self.assertEqual(config["captcha_solver_sessions"], {"a", "b"})

    def test_session_parser_supports_a_through_h_for_auto_catch(self):
        allowed = set("abcdefgh")
        parsed = main.parse_session_keys("a,b,c,d,e,f,g,h", "a", allowed)
        self.assertEqual(parsed, allowed)

    def test_adding_helperbot_layout_scopes_unified_collection_by_source_key(self):
        old_config = main.CONFIG
        try:
            main.CONFIG = {
                "direct_db_layout": "adding_helperbot",
                "direct_db_collection": "characters",
                "direct_db_dedicated_collection_no_filter": True,
            }
            profile = {
                "source_bot_key": "character_catcher",
                "items_collection": "items_character_catcher",
            }
            self.assertEqual(
                main.direct_db_base_filter(profile),
                {"source_key": "items_character_catcher"},
            )
            self.assertEqual(
                main.direct_db_base_filter(None),
                {"_id": {"$exists": False}},
            )
        finally:
            main.CONFIG = old_config

    def test_adding_helperbot_uid_query_checks_uid_array_and_legacy_fields(self):
        old_config = main.CONFIG
        try:
            main.CONFIG = {"direct_db_layout": "adding_helperbot"}
            query = main.build_direct_db_uid_query(["uid-small", "uid-large", "uid-small"])
            expected_uids = ["uid-small", "uid-large"]
            self.assertEqual(query["$or"][0], {"file_unique_ids": {"$in": expected_uids}})
            self.assertIn({"telegram_file_unique_id": {"$in": expected_uids}}, query["$or"])
            self.assertIn({"file_unique_id": {"$in": expected_uids}}, query["$or"])
        finally:
            main.CONFIG = old_config

    def test_media_uid_collection_includes_all_photo_sizes(self):
        from types import SimpleNamespace

        message = SimpleNamespace(
            photo=[
                SimpleNamespace(file_unique_id="uid-small"),
                SimpleNamespace(file_unique_id="uid-large"),
            ],
            video=None,
            animation=None,
            document=None,
            sticker=None,
        )
        self.assertEqual(
            main.get_media_file_unique_ids(message),
            ["uid-small", "uid-large"],
        )

    def test_auth_target_uses_replied_user_or_numeric_argument(self):
        from types import SimpleNamespace

        message = SimpleNamespace(reply_to_message=SimpleNamespace(from_user=SimpleNamespace(id=67890)))
        self.assertEqual(main.get_auth_target_user_id(message, "/auth"), 67890)

        message = SimpleNamespace(reply_to_message=None)
        self.assertEqual(main.get_auth_target_user_id(message, "/auth 12345"), 12345)
        self.assertIsNone(main.get_auth_target_user_id(message, "/auth"))
        self.assertIsNone(main.get_auth_target_user_id(message, "/auth -123"))

    def test_authorized_users_are_persisted_and_owner_ids_are_excluded(self):
        import tempfile

        old_authorized = set(main.AUTHORIZED_USERS)
        old_groups = main.SOURCE_GROUPS_CONFIG
        old_rarities = main.RARITY_CONFIG
        old_config = main.CONFIG
        old_path = main.BOT_CONFIG_FILE
        try:
            with tempfile.TemporaryDirectory() as temp_dir:
                main.BOT_CONFIG_FILE = os.path.join(temp_dir, "bot_config.json")
                main.CONFIG = {"owner_ids": {111}, "group_ids": set()}
                main.SOURCE_GROUPS_CONFIG = {}
                main.RARITY_CONFIG = {}
                main.AUTHORIZED_USERS.clear()
                main.AUTHORIZED_USERS.update({111, 222, 333})
                main.save_auto_config()
                main.AUTHORIZED_USERS.clear()
                main.init_auto_config()
                self.assertEqual(main.AUTHORIZED_USERS, {222, 333})
        finally:
            main.AUTHORIZED_USERS.clear()
            main.AUTHORIZED_USERS.update(old_authorized)
            main.SOURCE_GROUPS_CONFIG = old_groups
            main.RARITY_CONFIG = old_rarities
            main.CONFIG = old_config
            main.BOT_CONFIG_FILE = old_path

    def test_cancelled_sqlite_caller_keeps_lock_until_worker_finishes(self):
        async def scenario():
            main.db_lock = asyncio.Lock()
            worker_started = threading.Event()
            release_worker = threading.Event()
            second_started = threading.Event()

            def blocking_worker():
                worker_started.set()
                release_worker.wait(timeout=3)
                return "first"

            def second_worker():
                second_started.set()
                return "second"

            first = asyncio.create_task(main._run_db_locked(blocking_worker))
            self.assertTrue(await asyncio.to_thread(worker_started.wait, 1))
            first.cancel()

            second = asyncio.create_task(main._run_db_locked(second_worker))
            await asyncio.sleep(0.05)
            self.assertFalse(second_started.is_set())

            release_worker.set()
            with self.assertRaises(asyncio.CancelledError):
                await first
            self.assertEqual(await second, "second")
            self.assertTrue(second_started.is_set())

        asyncio.run(scenario())

    def test_shutdown_closes_every_resource_even_if_one_client_stop_fails(self):
        class FakeClient:
            def __init__(self, fail=False):
                self.is_connected = True
                self.fail = fail
                self.stop_called = False

            async def stop(self):
                self.stop_called = True
                self.is_connected = False
                if self.fail:
                    raise RuntimeError("simulated stop failure")

        class FakeMongoClient:
            def __init__(self):
                self.closed = False

            def close(self):
                self.closed = True

        async def scenario():
            old_clients = (main.app_a, main.app_b, main.app_c, main.app_d, main.app_e, main.app_f, main.app_g, main.app_h)
            old_db = main.db_conn
            old_mongo = main.direct_mongo_client
            old_items = main.direct_items_collection
            clients = (
                FakeClient(fail=True),
                FakeClient(),
                FakeClient(),
                FakeClient(),
                FakeClient(),
                FakeClient(),
                FakeClient(),
            )
            connection = sqlite3.connect(":memory:", check_same_thread=False)
            mongo = FakeMongoClient()

            main.app_a, main.app_b, main.app_c, main.app_d, main.app_e, main.app_f, main.app_g, main.app_h = clients
            main.db_conn = connection
            main.direct_mongo_client = mongo
            main.direct_items_collection = object()
            main.background_tasks.clear()
            main.conversation_tasks.clear()
            main.enabled_groups.add(-100123)

            background = main.spawn_background_task(asyncio.sleep(30))
            conversation = asyncio.create_task(asyncio.sleep(30))
            main.conversation_tasks[-100123] = conversation

            try:
                with self.assertLogs(level="ERROR") as captured_logs:
                    await main.shutdown_clients()
                await asyncio.sleep(0)

                self.assertTrue(any("Failed to stop Telegram session A" in item for item in captured_logs.output))
                self.assertTrue(all(client.stop_called for client in clients))
                self.assertTrue(background.cancelled())
                self.assertTrue(conversation.cancelled())
                self.assertFalse(main.background_tasks)
                self.assertFalse(main.conversation_tasks)
                self.assertNotIn(-100123, main.enabled_groups)
                self.assertIsNone(main.db_conn)
                with self.assertRaises(sqlite3.ProgrammingError):
                    connection.execute("SELECT 1")
                self.assertTrue(mongo.closed)
                self.assertIsNone(main.direct_mongo_client)
                self.assertIsNone(main.direct_items_collection)
            finally:
                main.app_a, main.app_b, main.app_c, main.app_d, main.app_e, main.app_f, main.app_g, main.app_h = old_clients
                main.db_conn = old_db
                main.direct_mongo_client = old_mongo
                main.direct_items_collection = old_items
                main.background_tasks.clear()
                main.conversation_tasks.clear()
                main.enabled_groups.discard(-100123)

        asyncio.run(scenario())

    def test_timed_out_cpu_worker_holds_concurrency_slot_until_thread_exits(self):
        async def scenario():
            main.captcha_solver_semaphore = asyncio.Semaphore(1)
            worker_started = threading.Event()
            release_worker = threading.Event()
            second_started = threading.Event()

            def blocking_worker():
                worker_started.set()
                release_worker.wait(timeout=3)
                return "first"

            def second_worker():
                second_started.set()
                return "second"

            first = asyncio.create_task(
                main.run_cpu_solver(blocking_worker, timeout=0.05)
            )
            self.assertTrue(await asyncio.to_thread(worker_started.wait, 1))
            with self.assertRaises(asyncio.TimeoutError):
                await first

            second = asyncio.create_task(
                main.run_cpu_solver(second_worker, timeout=1.0)
            )
            await asyncio.sleep(0.05)
            self.assertFalse(second_started.is_set())

            release_worker.set()
            self.assertEqual(await second, "second")
            self.assertTrue(second_started.is_set())

        asyncio.run(scenario())


if __name__ == "__main__":
    unittest.main()
