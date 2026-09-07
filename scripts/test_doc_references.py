"""Regression checks for Lean docstring references."""

from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).with_name("check-doc-references.py").resolve()


class DocReferenceTests(unittest.TestCase):
    def run_checker(self, text):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Vegas").mkdir()
            (root / "Vegas/Test.lean").write_text(text, encoding="utf-8")
            return subprocess.run([sys.executable, str(SCRIPT)], cwd=root,
                                  capture_output=True, text=True)

    def test_mixed_case_namespace_does_not_hide_stale_reference(self):
        result = self.run_checker("/-! `SomeNamespace.missing` -/\n")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("SomeNamespace.missing", result.stdout)

    def test_constructor_and_source_filename_are_accepted(self):
        result = self.run_checker(
            "inductive Participant where\n  | scheduler\n"
            "/-! `Participant.scheduler` in `Paper.lean`. -/\n"
        )
        self.assertEqual(result.returncode, 0, result.stdout)

    def test_stale_lowercase_dotted_reference_fails(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Vegas").mkdir()
            (root / "GameTheory/GameTheory").mkdir(parents=True)
            (root / "Vegas/Test.lean").write_text(
                "/-! A stale citation to `missing.name`. -/\n", encoding="utf-8"
            )
            result = subprocess.run(
                [sys.executable, str(SCRIPT)], cwd=root,
                capture_output=True, text=True,
            )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("unknown name `missing.name`", result.stdout)


if __name__ == "__main__":
    unittest.main()
