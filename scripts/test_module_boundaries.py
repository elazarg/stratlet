import importlib.util
from pathlib import Path
import tempfile
import unittest


SPEC = importlib.util.spec_from_file_location(
    "module_boundaries", Path(__file__).with_name("check-module-boundaries.py")
)
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)


class ModuleBoundaryTests(unittest.TestCase):
    def fixture(self, directory, modules, extra_config=""):
        root = Path(directory)
        (root / "lakefile.toml").write_text(
            'defaultTargets = ["Vegas", "VegasEVM", "VegasTests", "Paper"]\n'
            '[[lean_lib]]\nname = "Vegas"\n'
            '[[lean_lib]]\nname = "VegasEVM"\n'
            '[[lean_lib]]\nname = "VegasTests"\n'
            '[[lean_lib]]\nname = "Paper"\n' + extra_config, encoding="utf-8"
        )
        for module, text in modules.items():
            path = root.joinpath(*module.split(".")).with_suffix(".lean")
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text, encoding="utf-8")
        return root

    def test_comments_do_not_create_imports(self):
        self.assertEqual(CHECKER.imports(
            "/- import Bogus\n/- nested -/ -/\nimport Vegas.Core -- comment\n"
        ), ["Vegas.Core"])

    def test_downstream_import_and_orphan_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lakefile.toml").write_text(
                'defaultTargets = ["Vegas", "VegasEVM"]\n'
                '[[lean_lib]]\nname = "Vegas"\n'
                '[[lean_lib]]\nname = "VegasEVM"\n', encoding="utf-8"
            )
            (root / "Vegas.lean").write_text("import VegasEVM\n", encoding="utf-8")
            (root / "VegasEVM.lean").write_text("", encoding="utf-8")
            (root / "Vegas").mkdir()
            (root / "Vegas" / "Orphan.lean").write_text("", encoding="utf-8")
            errors = CHECKER.check(root)
            self.assertTrue(any("core imports downstream" in error for error in errors))
            self.assertTrue(any("Vegas.Orphan: unreachable" in error for error in errors))

    def test_missing_local_import_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory, {"Vegas": "import Vegas.Missing"})
            self.assertTrue(any("missing local import Vegas.Missing" in error
                                for error in CHECKER.check(root)))

    def test_carriers_and_runtime_cannot_import_adapters(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory, {
                "Vegas": "import Vegas.Machine.Program Vegas.Runtime.Adapter",
                "Vegas.Machine.Program": "import Vegas.Compile.Machine",
                "Vegas.Compile.Machine": "",
                "Vegas.Runtime.Adapter": "import Vegas.Game.Basic",
                "Vegas.Game.Basic": "",
            })
            errors = CHECKER.check(root)
            self.assertTrue(any("machine carrier imports compiler" in error for error in errors))
            self.assertTrue(any("runtime-general interface imports" in error for error in errors))

    def test_test_reachability_does_not_mask_incomplete_aggregator(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory, {
                "Vegas": "import Vegas.Game", "Vegas.Game": "",
                "Vegas.Game.Adapter": "", "VegasTests": "import Vegas.Game.Adapter",
            })
            errors = CHECKER.check(root)
            self.assertTrue(any("absent from Vegas.Game aggregator" in error for error in errors))
            self.assertFalse(any("unreachable" in error for error in errors))

    def test_all_default_targets_are_followed(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory, {
                "Vegas": "", "VegasEVM": "import Vegas", "VegasTests": "import VegasEVM",
                "Paper": "import VegasTests Paper.General", "Paper.General": "import Vegas",
            })
            self.assertEqual(CHECKER.check(root), [])

    def test_overlapping_libraries_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory, {"Vegas": "import Vegas.Core", "Vegas.Core": ""},
                                '[[lean_lib]]\nname = "Duplicate"\nroots = ["Vegas.Core"]\n')
            self.assertTrue(any("belongs to both" in error for error in CHECKER.check(root)))


if __name__ == "__main__":
    unittest.main()
