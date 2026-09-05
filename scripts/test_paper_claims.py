"""Regression checks for the paper audit's structural coverage guard."""

import importlib.util
import json
from pathlib import Path
import tempfile
import unittest


SPEC = importlib.util.spec_from_file_location(
    "paper_claims", Path(__file__).with_name("check-paper-claims.py")
)
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)


class PaperClaimsTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.paper = self.root / "overleaf"
        (self.root / "Vegas").mkdir()
        self.paper.mkdir()
        (self.root / "Vegas/Paper.lean").write_text("", encoding="utf-8")
        self.audit = self.root / "Paper.lean"
        self.audit.write_text(
            "namespace Vegas.Paper\n"
            "theorem witness : True := True.intro\n"
            "#guard_msgs (whitespace := lax) in\n"
            "#print axioms Vegas.Paper.witness\n"
            "end Vegas.Paper\n", encoding="utf-8"
        )
        self.registry = self.root / "paper-claims.json"
        self.registry.write_text(json.dumps({"thm:witness": ["Vegas.Paper.witness"]}),
                                 encoding="utf-8")
        self.main = self.paper / "main.tex"
        self.main.write_text(
            r"\begin{theorem}\label{thm:witness}Claim.\end{theorem}", encoding="utf-8"
        )

    def check(self):
        return CHECKER.check(self.root, self.paper)

    def test_valid_registry(self):
        self.assertEqual(self.check(), [])

    def test_numbered_claim_requires_mapping(self):
        with self.main.open("a", encoding="utf-8") as stream:
            stream.write(r"\begin{lemma}\label{lem:new}New.\end{lemma}")
        self.assertTrue(any("no Lean mapping: lem:new" in error for error in self.check()))

    def test_numbered_claim_requires_label(self):
        self.main.write_text(r"\begin{theorem}Unlabeled.\end{theorem}", encoding="utf-8")
        self.assertTrue(any("needs exactly one" in error for error in self.check()))

    def test_removed_claim_is_stale(self):
        self.main.write_text("", encoding="utf-8")
        self.assertTrue(any("Stale registry entry" in error for error in self.check()))

    def test_missing_declaration(self):
        self.audit.write_text("", encoding="utf-8")
        self.assertTrue(any("no audit theorem" in error for error in self.check()))

    def test_missing_pin(self):
        self.audit.write_text("namespace Vegas.Paper\ntheorem witness : True := True.intro\n",
                              encoding="utf-8")
        self.assertTrue(any("no guarded axiom pin" in error for error in self.check()))

    def test_comments_cannot_supply_declarations_or_pins(self):
        text = self.audit.read_text(encoding="utf-8")
        self.audit.write_text("/- outer /- nested -/\n" + text + "-/", encoding="utf-8")
        self.assertTrue(any("no audit theorem" in error for error in self.check()))

    def test_only_active_inputs_count(self):
        text = self.main.read_text(encoding="utf-8")
        (self.paper / "section.tex").write_text(text, encoding="utf-8")
        (self.paper / "archive.tex").write_text(r"\begin{theorem}Old.\end{theorem}",
                                                encoding="utf-8")
        self.main.write_text("\\input{section}\n% \\input{archive}\n", encoding="utf-8")
        self.assertEqual(self.check(), [])

    def test_prose_tags_are_checked(self):
        with self.main.open("a", encoding="utf-8") as stream:
            stream.write("\n% lean-claim: prose:new\n")
        self.assertTrue(any("no Lean mapping: prose:new" in error for error in self.check()))

    def test_duplicate_claim(self):
        with self.main.open("a", encoding="utf-8") as stream:
            stream.write("\n% lean-claim: thm:witness\n")
        self.assertTrue(any("Duplicate paper claim" in error for error in self.check()))

    def test_missing_checkout_fails_by_default(self):
        self.assertTrue(any("Missing active paper" in error for error in
                            CHECKER.check(self.root, self.root / "missing")))


if __name__ == "__main__":
    unittest.main()
