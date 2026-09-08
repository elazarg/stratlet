"""Regression checks for the paper audit's structural coverage guard."""

import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
import zipfile


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
        (self.root / "Paper").mkdir()
        self.paper.mkdir()
        for name in CHECKER.AUDIT_FILES:
            (self.root / name).write_text("", encoding="utf-8")
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
        self.write_snapshot()

    def write_snapshot(self, extra=None):
        files = {"main.tex": CHECKER.sha256(self.main)}
        if extra:
            files.update(extra)
        (self.root / CHECKER.SNAPSHOT_FILE).write_text(json.dumps({
            "revision": "abc123", "files": files,
        }), encoding="utf-8")

    def check(self):
        return CHECKER.check(self.root, self.paper)

    def test_valid_plain_export(self):
        self.assertEqual(self.check(), [])

    def test_source_audit_is_indexed(self):
        source_audit = self.root / "Paper/Source.lean"
        source_audit.write_text(self.audit.read_text(encoding="utf-8"), encoding="utf-8")
        self.audit.write_text("", encoding="utf-8")
        self.assertEqual(self.check(), [])

    def bibliography_fixture(self, active, names):
        self.main.write_text(self.main.read_text(encoding="utf-8") +
                             "\n\\bibliography{" + active + "}\n", encoding="utf-8")
        files = {}
        for name in names:
            path = self.paper / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("@article{example, title={Example}}\n", encoding="utf-8")
            files[name] = CHECKER.sha256(path)
        self.write_snapshot(files)

    def test_ambiguous_bibliography_filename_is_rejected(self):
        self.bibliography_fixture("references", ["references.bib", "Long/references.bib"])
        self.assertTrue(any("Ambiguous bibliography filename references.bib" in error
                            for error in self.check()))

    def test_unique_bibliography_with_archived_database_is_accepted(self):
        self.bibliography_fixture("vegas-paper", ["vegas-paper.bib", "Long/references.bib"])
        self.assertEqual(self.check(), [])

    def test_active_bibliography_must_be_in_snapshot(self):
        self.bibliography_fixture("missing", [])
        self.assertTrue(any("Active bibliography absent from snapshot manifest: missing.bib"
                            in error for error in self.check()))

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
        self.write_snapshot({"section.tex": CHECKER.sha256(self.paper / "section.tex")})
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

    def test_tampered_export_fails(self):
        self.main.write_text("tampered", encoding="utf-8")
        self.assertTrue(any("digest mismatch" in error for error in self.check()))

    def test_missing_manifest_file_fails(self):
        self.write_snapshot({"missing.tex": "0" * 64})
        self.assertTrue(any("snapshot file missing" in error for error in self.check()))

    def test_untracked_active_input_fails(self):
        child = self.paper / "extra.tex"
        child.write_text(r"\begin{theorem}\label{thm:witness}Claim.\end{theorem}",
                         encoding="utf-8")
        self.main.write_text(r"\input{extra}", encoding="utf-8")
        self.write_snapshot()
        self.assertTrue(any("absent from snapshot manifest" in error for error in self.check()))

    def test_wrong_git_revision_fails(self):
        subprocess.run(["git", "init", "-q", str(self.paper)], check=True)
        subprocess.run(["git", "-C", str(self.paper), "config", "user.email",
                        "test@example.invalid"], check=True)
        subprocess.run(["git", "-C", str(self.paper), "config", "user.name", "Test"],
                       check=True)
        subprocess.run(["git", "-C", str(self.paper), "add", "main.tex"], check=True)
        subprocess.run(["git", "-C", str(self.paper), "commit", "-qm", "fixture"],
                       check=True)
        errors = self.check()
        self.assertTrue(any("Paper revision mismatch" in error for error in errors), errors)

    def test_plain_git_archive_validates(self):
        source = self.root / "source"
        source.mkdir()
        (source / "main.tex").write_text(self.main.read_text(encoding="utf-8"),
                                          encoding="utf-8")
        subprocess.run(["git", "init", "-q", str(source)], check=True)
        subprocess.run(["git", "-C", str(source), "config", "user.email",
                        "test@example.invalid"], check=True)
        subprocess.run(["git", "-C", str(source), "config", "user.name", "Test"],
                       check=True)
        subprocess.run(["git", "-C", str(source), "add", "main.tex"], check=True)
        subprocess.run(["git", "-C", str(source), "commit", "-qm", "fixture"],
                       check=True)
        (self.root / CHECKER.SNAPSHOT_FILE).write_text(
            json.dumps(CHECKER.make_snapshot(source)), encoding="utf-8"
        )
        archive = self.root / "paper.zip"
        export = self.root / "export"
        subprocess.run(["git", "-C", str(source), "archive", "--format=zip",
                        f"--output={archive}", "HEAD"], check=True)
        with zipfile.ZipFile(archive) as zipped:
            zipped.extractall(export)
        self.assertEqual(CHECKER.check(self.root, export), [])


if __name__ == "__main__":
    unittest.main()
