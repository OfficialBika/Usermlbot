import ast
import re
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = (ROOT / "main.py").read_text(encoding="utf-8")
ENV_EXAMPLE = (ROOT / ".env.example").read_text(encoding="utf-8")
TREE = ast.parse(SOURCE, filename="main.py")


def top_level_function(name):
    for node in TREE.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name == name:
            return node
    raise AssertionError(f"Function not found: {name}")


def calls_named(node, name):
    return [
        child for child in ast.walk(node)
        if isinstance(child, ast.Call)
        and isinstance(child.func, ast.Name)
        and child.func.id == name
    ]


def awaited_call_nodes(node, name):
    parents = {}
    for parent in ast.walk(node):
        for child in ast.iter_child_nodes(parent):
            parents[child] = parent
    return [
        call for call in calls_named(node, name)
        if isinstance(parents.get(call), ast.Await)
    ]


class RuntimeSafetyContracts(unittest.TestCase):
    def test_main_is_syntax_valid(self):
        # TREE is parsed at import time; this test makes the CI intent explicit.
        self.assertIsInstance(TREE, ast.Module)

    def test_main_always_runs_shutdown_after_resource_setup(self):
        main = top_level_function("main")
        lifecycle = [
            node for node in ast.walk(main)
            if isinstance(node, ast.Try)
            and any(
                isinstance(item, ast.Expr)
                and isinstance(item.value, ast.Await)
                and isinstance(item.value.value, ast.Call)
                and isinstance(item.value.value.func, ast.Name)
                and item.value.value.func.id == "shutdown_clients"
                for item in node.finalbody
            )
        ]
        self.assertTrue(lifecycle, "main() must call shutdown_clients() in a finally block")
        protected_calls = {
            name: any(
                calls_named(ast.Module(body=block.body, type_ignores=[]), name)
                for block in lifecycle
            )
            for name in ("init_database", "init_auto_config", "register_handlers", "init_direct_db", "start_health_server")
        }
        self.assertTrue(all(protected_calls.values()), protected_calls)

    def test_sqlite_helpers_use_cancellation_safe_lock_wrapper(self):
        for name in ("db_execute", "db_fetchall", "db_fetchone", "load_learned_digit_templates", "_save_captcha_templates"):
            function = top_level_function(name)
            self.assertTrue(calls_named(function, "_run_db_locked"), name)

        runner = top_level_function("_run_db_locked")
        self.assertTrue(
            any(
                isinstance(node, ast.AsyncWith)
                and any(
                    isinstance(item.context_expr, ast.Name) and item.context_expr.id == "db_lock"
                    for item in node.items
                )
                for node in ast.walk(runner)
            )
        )

    def test_cancelled_sqlite_caller_waits_for_worker_before_unlocking(self):
        helper = top_level_function("_await_thread_completion")
        self.assertTrue(
            any(
                isinstance(node, ast.Call)
                and isinstance(node.func, ast.Attribute)
                and node.func.attr == "shield"
                for node in ast.walk(helper)
            )
        )
        cancellation_handlers = [
            handler for node in ast.walk(helper) if isinstance(node, ast.Try)
            for handler in node.handlers
            if (
                isinstance(handler.type, ast.Attribute)
                and handler.type.attr == "CancelledError"
            )
        ]
        self.assertTrue(cancellation_handlers)
        self.assertTrue(any(
            isinstance(node, ast.Await) and isinstance(node.value, ast.Name) and node.value.id == "worker"
            for handler in cancellation_handlers for node in ast.walk(handler)
        ))

    def test_shutdown_cancels_tasks_before_stopping_clients_and_closing_db(self):
        shutdown = top_level_function("shutdown_clients")
        cancel_calls = [
            node for node in ast.walk(shutdown)
            if isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr == "cancel"
        ]
        gathers = [
            node for node in ast.walk(shutdown)
            if isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr == "gather"
        ]
        stop_gather = next(
            (
                node for node in gathers
                if any(
                    isinstance(child, ast.Call)
                    and isinstance(child.func, ast.Name)
                    and child.func.id == "_stop_client"
                    for child in ast.walk(node)
                )
            ),
            None,
        )
        close_calls = calls_named(shutdown, "_await_thread_completion")
        self.assertTrue(cancel_calls)
        self.assertGreaterEqual(len(gathers), 2)
        self.assertIsNotNone(stop_gather)
        self.assertTrue(close_calls)
        self.assertLess(min(node.lineno for node in cancel_calls), min(node.lineno for node in gathers))
        self.assertLess(min(node.lineno for node in gathers), stop_gather.lineno)
        self.assertLess(stop_gather.lineno, min(node.lineno for node in close_calls))

    def test_timed_out_captcha_worker_keeps_concurrency_slot_until_exit(self):
        function = top_level_function("run_cpu_solver")
        self.assertTrue(any(
            isinstance(node, ast.Await)
            and isinstance(node.value, ast.Call)
            and isinstance(node.value.func, ast.Attribute)
            and node.value.func.attr == "acquire"
            for node in ast.walk(function)
        ))
        self.assertTrue(any(
            isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr == "shield"
            for node in ast.walk(function)
        ))
        self.assertTrue(any(
            isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr == "add_done_callback"
            for node in ast.walk(function)
        ))
        self.assertIn("release_when_worker_finishes", ast.unparse(function))

    def test_captcha_cpu_solver_functions_remain_synchronous(self):
        for name in ("get_captcha_best_guess", "solve_captcha_image_auto"):
            function = top_level_function(name)
            self.assertIsInstance(function, ast.FunctionDef)
            self.assertFalse(any(isinstance(node, ast.Await) for node in ast.walk(function)), name)

        self.assertIsInstance(top_level_function("solve_by_learned_template_match"), ast.AsyncFunctionDef)
        self.assertEqual(
            len(awaited_call_nodes(top_level_function("handle_captcha_solver"), "solve_by_learned_template_match")),
            1,
        )

    def test_captcha_and_delayed_delete_tasks_are_tracked(self):
        for function_name in ("handle_general_message", "handle_direct_db_catch", "handle_responder_dm"):
            function = top_level_function(function_name)
            if function_name == "handle_general_message":
                self.assertTrue(calls_named(function, "spawn_background_task"))
            else:
                self.assertTrue(calls_named(function, "spawn_background_task"))

    def test_mongo_initialization_failure_closes_partial_client(self):
        function = top_level_function("init_direct_db")
        self.assertTrue(any(
            isinstance(node, ast.Assign)
            and any(isinstance(target, ast.Name) and target.id == "direct_mongo_client" for target in node.targets)
            and isinstance(node.value, ast.Constant) and node.value.value is None
            for node in ast.walk(function)
        ))
        self.assertTrue(any(
            isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr == "close"
            for node in ast.walk(function)
        ))

    def test_health_route_matches_render_blueprint(self):
        self.assertIn('application.router.add_get("/health", health_check)', SOURCE)
        render = (ROOT / "render.yaml").read_text(encoding="utf-8")
        self.assertIn("healthCheckPath: /health", render)

    def test_session_c_and_d_remain_human_chat_only(self):
        self.assertIn('os.getenv("HUMAN_CHAT_SESSIONS", "a,b,c,d")', SOURCE)
        self.assertIn('{"a", "b", "c", "d"}', SOURCE)
        self.assertIn('{"a", "b"}', SOURCE)

    def test_env_example_does_not_contain_unknown_runtime_keys(self):
        keys = {
            match.group(1)
            for line in ENV_EXAMPLE.splitlines()
            if not line.lstrip().startswith("#")
            if (match := re.match(r"^([A-Z][A-Z0-9_]*)=", line.strip()))
        }
        unused = sorted(key for key in keys if f'"{key}"' not in SOURCE and f"'{key}'" not in SOURCE)
        self.assertEqual(unused, [], f"Unused .env.example settings: {unused}")

    def test_gitignore_protects_credentials_and_runtime_state(self):
        ignore = (ROOT / ".gitignore").read_text(encoding="utf-8")
        for pattern in (".env", "*.session", "*.db", "bot_config.json", "logs/*.log"):
            self.assertIn(pattern, ignore)
        self.assertIn("!.env.example", ignore)

    def test_optional_automation_is_disabled_in_example(self):
        for setting in (
            "AUTO_FORWARD_ENABLED=false",
            "DIRECT_DB_CATCH_ENABLED=false",
            "CAPTCHA_SOLVER_ENABLED=false",
            "CAPTCHA_AUTO_APPROVE=false",
        ):
            self.assertIn(setting, ENV_EXAMPLE)


if __name__ == "__main__":
    unittest.main()
