import importlib.util
from pathlib import Path
import unittest


SPEC = importlib.util.spec_from_file_location(
    "lean_options", Path(__file__).with_name("check-lean-options.py")
)
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)


class LeanOptionTests(unittest.TestCase):
    def test_strict_central_options_pass(self):
        self.assertEqual(CHECKER.check_central_options({
            "autoImplicit": False,
            "relaxedAutoImplicit": False,
            "warningAsError": True,
        }), [])

    def test_missing_options_fail(self):
        self.assertEqual(len(CHECKER.check_central_options({})), 3)

    def test_relaxed_flag_alone_does_not_disable_implicit_binders(self):
        errors = CHECKER.check_central_options({
            "relaxedAutoImplicit": False,
            "warningAsError": True,
        })
        self.assertEqual(len(errors), 1)
        self.assertIn("autoImplicit", errors[0])

    def test_each_required_option_is_enforced(self):
        valid = {
            "autoImplicit": False,
            "relaxedAutoImplicit": False,
            "warningAsError": True,
        }
        for name, value in valid.items():
            with self.subTest(option=name):
                errors = CHECKER.check_central_options({**valid, name: not value})
                self.assertEqual(len(errors), 1)
                self.assertIn(name, errors[0])


if __name__ == "__main__":
    unittest.main()
