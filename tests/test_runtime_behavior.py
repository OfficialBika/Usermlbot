import asyncio
import os
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
        self.assertEqual(config["human_chat_sessions"], {"a", "b", "c", "d"})
        self.assertEqual(config["auto_catch_sessions"], {"a", "b"})
        self.assertEqual(config["captcha_solver_sessions"], {"a", "b"})

    def test_session_parser_rejects_c_and_d_for_auto_catch(self):
        parsed = main.parse_session_keys("a,b,c,d", "a", {"a", "b"})
        self.assertEqual(parsed, {"a", "b"})

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
