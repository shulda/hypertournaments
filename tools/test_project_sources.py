"""Regressions for source checks used before installing Lean in CI."""
import unittest

from project_sources import proof_placeholders, source_imports


class ProofSourceChecks(unittest.TestCase):
    def test_mathematical_prose_is_not_a_tactic(self):
        self.assertEqual(proof_placeholders(
            '/- The two central types admit a pair. /- sorry -/ -/\n'
            '-- axiom is discussed here\n'
            'example : True := by trivial\n'), [])

    def test_quoted_examples_are_not_proof_tokens(self):
        self.assertEqual(proof_placeholders(
            'def message := "say \\"sorry\\"; admit and axiom"\n'), [])

    def test_actual_holes_and_axioms_are_rejected(self):
        self.assertEqual(proof_placeholders(
            'example : True := by\n  sorry\n'), [(2, 'sorry')])
        self.assertEqual(proof_placeholders(
            'example : True := by (admit)\n'), [(1, 'admit')])
        self.assertEqual(proof_placeholders(
            'axiom unchecked : False\n'), [(1, 'axiom')])

    def test_comments_do_not_hide_following_real_holes(self):
        self.assertEqual(proof_placeholders(
            '/- admit /- nested -/ -/\nexample : True := by sorry\n'),
            [(2, 'sorry')])

    def test_identifier_parts_are_not_keywords(self):
        self.assertEqual(proof_placeholders(
            'def sorry_name := 0\ndef admit\' := 1\n'), [])

    def test_inline_comments_separate_tokens(self):
        self.assertEqual(proof_placeholders(
            'example : True := by/- explanation -/sorry\n'), [(1, 'sorry')])
        self.assertEqual(proof_placeholders('sor/- explanation -/ry'), [])

    def test_quote_character_does_not_hide_following_hole(self):
        text = '''def quote : Char := '"'
example : True := by sorry
'''
        self.assertEqual(proof_placeholders(text), [(2, 'sorry')])

    def test_raw_backslash_does_not_escape_its_closing_quote(self):
        text = r'def slash : String := r"\"' + '\nexample : True := by sorry\n'
        self.assertEqual(proof_placeholders(text), [(2, 'sorry')])

    def test_raw_string_hash_delimiters_mask_embedded_quotes(self):
        text = r'def prose : String := r##"\" sorry admit axiom "##'
        self.assertEqual(proof_placeholders(text), [])
        self.assertEqual(proof_placeholders(text + '\nexample : True := by sorry\n'),
                         [(2, 'sorry')])

    def test_import_scan_keeps_its_comment_and_string_behavior(self):
        self.assertEqual(source_imports(
            '/- import Mathlib /- nested -/ -/\n'
            'import Hypertournaments.Basic\n'
            'def message := "import Mathlib.Tactic"\n'),
            ['Hypertournaments.Basic'])


if __name__ == '__main__':
    unittest.main()
