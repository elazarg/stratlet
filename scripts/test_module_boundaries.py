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

    def test_two_layer_cycle_reports_import_witnesses(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory, {
                "Vegas": "import Vegas.Alpha.One Vegas.Beta.Two",
                "Vegas.Alpha.One": "import Vegas.Beta.One",
                "Vegas.Alpha.Two": "",
                "Vegas.Beta.One": "",
                "Vegas.Beta.Two": "import Vegas.Alpha.Two",
            })
            errors = CHECKER.check(root)
            report = next(error for error in errors if "sibling layer import cycle" in error)
            self.assertIn("Vegas.Alpha.One imports Vegas.Beta.One", report)
            self.assertIn("Vegas.Beta.Two imports Vegas.Alpha.Two", report)

    def test_three_module_cycle_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory, {
                "Vegas": "import Vegas.Core.A",
                "Vegas.Core.A": "import Vegas.Core.B",
                "Vegas.Core.B": "import Vegas.Core.C",
                "Vegas.Core.C": "import Vegas.Core.A",
            })
            errors = CHECKER.check(root)
            report = next(error for error in errors if "local module import cycle" in error)
            self.assertIn("Vegas.Core.A imports Vegas.Core.B", report)
            self.assertIn("Vegas.Core.C imports Vegas.Core.A", report)

    def test_acyclic_diamond_is_accepted(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory, {
                "Vegas": "import Vegas.Top",
                "Vegas.Top": "import Vegas.Left Vegas.Right",
                "Vegas.Left": "import Vegas.Bottom",
                "Vegas.Right": "import Vegas.Bottom",
                "Vegas.Bottom": "",
            })
            self.assertEqual(CHECKER.check(root), [])

    def test_aggregators_nested_siblings_and_external_imports(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory, {
                "Vegas": "import Vegas.Game Mathlib.Data.Nat.Basic",
                "Vegas.Game": "import Vegas.Game.Basic Vegas.Game.Deep.Left.A "
                              "Vegas.Game.Deep.Right.B",
                "Vegas.Game.Basic": "",
                "Vegas.Game.Deep.Left.A": "import Vegas.Game.Shared.Value",
                "Vegas.Game.Deep.Right.B": "import Vegas.Game.Deep.Left.A",
                "Vegas.Game.Shared.Value": "",
            })
            self.assertEqual(CHECKER.check(root), [])

    def test_three_layer_cycle_with_acyclic_module_graph(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory, {
                "Vegas": "import Vegas.Alpha.A Vegas.Beta.B Vegas.Gamma.C",
                "Vegas.Alpha.A": "import Vegas.Beta.Leaf",
                "Vegas.Beta.B": "import Vegas.Gamma.Leaf",
                "Vegas.Beta.Leaf": "",
                "Vegas.Gamma.C": "import Vegas.Alpha.Leaf",
                "Vegas.Gamma.Leaf": "",
                "Vegas.Alpha.Leaf": "",
            })
            errors = CHECKER.check(root)
            self.assertFalse(any("local module import cycle" in error for error in errors))
            self.assertTrue(any("Vegas.Alpha -> Vegas.Beta -> Vegas.Gamma -> Vegas.Alpha"
                                in error for error in errors))

    def test_nested_sibling_cycle_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = self.fixture(directory, {
                "Vegas": "import Vegas.Game",
                "Vegas.Game": "import Vegas.Game.Deep.Left.A Vegas.Game.Deep.Right.B",
                "Vegas.Game.Deep.Left.A": "import Vegas.Game.Deep.Right.Leaf",
                "Vegas.Game.Deep.Left.Leaf": "",
                "Vegas.Game.Deep.Right.B": "import Vegas.Game.Deep.Left.Leaf",
                "Vegas.Game.Deep.Right.Leaf": "",
            })
            errors = CHECKER.check(root)
            self.assertTrue(any("sibling layer import cycle under Vegas.Game.Deep" in error
                                for error in errors))


if __name__ == "__main__":
    unittest.main()
