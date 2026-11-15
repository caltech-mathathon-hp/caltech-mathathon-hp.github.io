"""Focused tests: python3 -B checks/test_verify.py (no Lean/Lake required)."""

import sys
import unittest

sys.dont_write_bytecode = True

import verify


class SourceChecks(unittest.TestCase):
    def test_comments_and_strings_preserve_line_positions(self):
        source = ('/- outer sorry\n /- axiom inner -/ admit -/\n'
                  '-- native_decide\n'
                  'def text := "unsafe \\"sorry\\""\n'
                  'theorem sound : True := by trivial\n')
        code = verify.lean_code(source)
        self.assertEqual(len(source), len(code))
        self.assertEqual(source.count("\n"), code.count("\n"))
        self.assertIsNone(verify.FORBIDDEN.search(code))
        self.assertIn("theorem sound", code)

    def test_raw_string_and_interpolated_literal_text(self):
        source = 'def x := r##"sorry " axiom"##\ndef y := s!"unsafe {{sorry}} {1 + 2}"'
        code = verify.lean_code(source)
        self.assertIsNone(verify.FORBIDDEN.search(code))
        self.assertIn("1 + 2", code)

    def test_interpolated_code_is_scanned(self):
        with self.assertRaisesRegex(verify.VerificationError, "sorry"):
            verify.scan_lean('def x := s!"value {by sorry}"', "Bad.lean", "")

    def test_unterminated_literals_and_comments_fail(self):
        for source in ['/- nested /- x -/', 'def x := "text', 's!"{(1 + 2)']:
            with self.subTest(source=source), self.assertRaises(verify.VerificationError):
                verify.lean_code(source)

    def test_proof_bypasses_and_suppression_fail(self):
        for source in ["by sorry", "by admit", "axiom lie : False", "unsafe def x := 1",
                       "@[extern x] def x := 1", "@[implemented_by x] def y := 1",
                       "by native_decide", "opaque x : Nat := 1", "@[csimp] theorem x := 1",
                       "proof_wanted x : False", "#eval x", "run_elab x", "run_cmd x",
                       "local macro x := y", "set_option linter.unusedVariables false"]:
            with self.subTest(source=source), self.assertRaises(verify.VerificationError):
                verify.scan_lean(source, "Bad.lean", "")

    def test_print_axioms_and_kernel_decide_are_allowed(self):
        verify.scan_lean('#print axioms Example\nexample : True := by decide +kernel', "Good.lean", "")

    def test_imports_ignore_comments_and_strings(self):
        source = ('/- import Fake.Hidden -/\nimport ProteinFolding.Common.Statement Mathlib.Data.Nat.Basic -- ignored\n'
                  'def x := "import Fake.String"\n')
        self.assertEqual(verify.imports_of(verify.lean_code(source)),
                         ["ProteinFolding.Common.Statement", "Mathlib.Data.Nat.Basic"])

    def test_duplicate_json_keys_and_escaping_paths_fail(self):
        with self.assertRaises(verify.VerificationError):
            verify.read_json(b'{"path":"first","path":"second"}')
        for path in ["../escape", "/absolute", "C:/absolute", "a\\b", "a/../b", "a//b"]:
            with self.subTest(path=path), self.assertRaises(verify.VerificationError):
                verify.safe_file(verify.PACKAGE, path)


class AxiomReports(unittest.TestCase):
    @staticmethod
    def reports():
        return "\n".join("'{}' depends on axioms: [propext,\n Classical.choice, Quot.sound]".format(name)
                         for name in verify.EXPECTED_REPORTS) + "\n"

    def test_exact_reports_accept_standard_axioms(self):
        self.assertEqual(verify.verify_axiom_reports(self.reports()), verify.ALLOWED_AXIOMS)

    def test_missing_duplicate_extra_and_unexpected_axioms_fail(self):
        good = self.reports()
        duplicate = "'{}' does not depend on any axioms\n".format(verify.EXPECTED_REPORTS[0])
        for output in [good + duplicate, good.replace(verify.EXPECTED_REPORTS[0], "Other.theorem"),
                       good.replace("Quot.sound", "sorryAx", 1), good + "PANIC: failure\n",
                       good + "Example.lean:1:0: error: failed\n", ""]:
            with self.subTest(output=output), self.assertRaises(verify.VerificationError):
                verify.verify_axiom_reports(output)


if __name__ == "__main__":
    unittest.main()
