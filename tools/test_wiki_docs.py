"""Failure-mode checks for the portable Wiki/theorem catalogue generator."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

import wiki_docs as wiki


class WikiDocumentationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        for directory in ['docs/catalogue', 'docs/wiki-src', 'Hypertournaments']:
            (self.root / directory).mkdir(parents=True)
        self.write_json('docs/catalogue/papers.json', {
            'schema_version': 1, 'repository': 'owner/formalization',
            'source_ref': 'main', 'source_revision': 'paper-pin',
            'papers': [{'id': 'main', 'title': 'The paper', 'author': 'The author',
                        'filename': 'paper.tex', 'wiki_page': 'Main-article',
                        'description': 'The main mathematical paper.'}]})
        self.write_json('docs/catalogue/source-labels.json', {
            'source_revision': 'paper-pin',
            'papers': {'main': {'thm:main': {'number': '1.2', 'kind': 'Theorem'}}}})
        self.entry = {'id': 'main-theorem', 'label': 'thm:main', 'kind': 'theorem',
                      'title': 'A theorem', 'scope': 'All finite inputs.',
                      'status': 'proved', 'notes': '',
                      'declarations': [{'name': 'Hypertournaments.Native.result',
                                        'module': 'Hypertournaments.Core'}]}
        self.write_entries([self.entry])
        (self.root / 'Hypertournaments/Core.lean').write_text(
            'namespace Hypertournaments\nsection\nnamespace Native\n'
            '/- A fake declaration: theorem result : False := bad -/\n'
            'theorem result : True := by trivial\n'
            'end Native\nend\nend Hypertournaments\n')
        (self.root / 'docs/wiki-src/Home.md').write_text(
            '# Home\n\n[Statements](Main-article)\n\n{{lean:Hypertournaments.Native.result}}\n')
        (self.root / 'docs/wiki-src/Main-article.md').write_text(
            '# Statements\n\n{{table:main}}\n\n{{file:Hypertournaments/Core.lean}}\n')

    def write_json(self, path, data):
        (self.root / path).write_text(json.dumps(data))

    def write_entries(self, entries):
        self.write_json('docs/catalogue/main.json', {'document': 'main', 'entries': entries})

    def test_render_checks_real_line_and_is_portable(self):
        outputs = wiki.build_outputs(self.root)
        registry = json.loads(outputs[Path('docs/theorem-map.json')])
        entry = registry['entries'][0]
        self.assertEqual(entry['number'], '1.2')
        self.assertEqual(entry['declarations'][0]['line'], 5)
        self.assertTrue(entry['primary_url'].endswith('Hypertournaments/Core.lean#L5'))
        self.assertIn('#check Hypertournaments.Native.result', outputs[Path('docs/CheckTheoremMap.lean')])
        relocated = wiki.build_outputs(self.root, 'another/clean-repo', 'v1.0')
        page = relocated[Path('docs/wiki/Main-article.md')]
        self.assertIn('https://github.com/another/clean-repo/blob/v1.0/', page)
        self.assertNotIn('owner/formalization', page)
        wiki.write_or_check(self.root, outputs, False)
        wiki.write_or_check(self.root, outputs, True)

    def test_missing_declaration_is_not_found_in_comment(self):
        path = self.root / 'Hypertournaments/Core.lean'
        path.write_text('namespace Hypertournaments.Native\n/- theorem result : True := by trivial -/\nend Hypertournaments.Native\n')
        with self.assertRaisesRegex(wiki.WikiError, 'Declaration not defined'):
            wiki.build_outputs(self.root)

    def test_wrong_namespace_is_not_accepted_by_basename(self):
        path = self.root / 'Hypertournaments/Core.lean'
        path.write_text('namespace Different\ntheorem result : True := by trivial\nend Different\n')
        with self.assertRaisesRegex(wiki.WikiError, 'Declaration not defined'):
            wiki.build_outputs(self.root)

    def test_nested_namespace_and_qualified_names(self):
        path = self.root / 'Hypertournaments/Core.lean'
        path.write_text('namespace Hypertournaments\nsection named\n@[simp] theorem Native.result : True := by trivial\nend named\nend Hypertournaments\n')
        self.assertEqual(wiki.declaration_location(self.root, 'Hypertournaments.Native.result',
                                                  'Hypertournaments.Core')['line'], 3)

    def test_duplicate_statement_and_label_are_rejected(self):
        self.write_entries([self.entry, dict(self.entry)])
        with self.assertRaisesRegex(wiki.WikiError, 'duplicate entry id'):
            wiki.build_outputs(self.root)
        other = dict(self.entry, id='another-id')
        self.write_entries([self.entry, other])
        with self.assertRaisesRegex(wiki.WikiError, 'Duplicate or invalid source label'):
            wiki.build_outputs(self.root)

    def test_unknown_source_label_and_revision_drift_are_rejected(self):
        self.entry['label'] = 'thm:unknown'
        self.write_entries([self.entry])
        with self.assertRaisesRegex(wiki.WikiError, 'Unknown source label'):
            wiki.build_outputs(self.root)
        config = json.loads((self.root / 'docs/catalogue/papers.json').read_text())
        config['source_revision'] = 'changed-pin'
        self.write_json('docs/catalogue/papers.json', config)
        with self.assertRaisesRegex(wiki.WikiError, 'revision disagree'):
            wiki.build_outputs(self.root)

    def test_variants_require_scope_explanation(self):
        self.entry['status'] = 'proof-variant'
        self.write_entries([self.entry])
        with self.assertRaisesRegex(wiki.WikiError, 'must explain'):
            wiki.build_outputs(self.root)

    def test_stale_source_lines_and_pages_fail_check(self):
        outputs = wiki.build_outputs(self.root)
        wiki.write_or_check(self.root, outputs, False)
        source = self.root / 'Hypertournaments/Core.lean'
        source.write_text('\n' + source.read_text())
        new_outputs = wiki.build_outputs(self.root)
        with self.assertRaisesRegex(wiki.WikiError, 'Generated documentation is stale'):
            wiki.write_or_check(self.root, new_outputs, True)
        wiki.write_or_check(self.root, new_outputs, False)
        (self.root / 'docs/wiki/Old-page.md').write_text(wiki.GENERATED + 'An obsolete page.\n')
        with self.assertRaisesRegex(wiki.WikiError, 'Old-page'):
            wiki.write_or_check(self.root, new_outputs, True)
        wiki.write_or_check(self.root, new_outputs, False)
        self.assertFalse((self.root / 'docs/wiki/Old-page.md').exists())

    def test_broken_internal_page_and_unknown_macros_are_rejected(self):
        page = self.root / 'docs/wiki-src/Home.md'
        page.write_text('[Missing](Not-a-page)\n')
        with self.assertRaisesRegex(wiki.WikiError, 'unknown Wiki page link'):
            wiki.build_outputs(self.root)
        page.write_text('{{unknown:thing}}\n')
        with self.assertRaisesRegex(wiki.WikiError, 'Unknown Wiki macro'):
            wiki.build_outputs(self.root)
        page.write_text('{{lean:Unknown.symbol}}\n')
        with self.assertRaisesRegex(wiki.WikiError, 'Unregistered Lean symbol'):
            wiki.build_outputs(self.root)

    def test_missing_files_and_source_url_literals_are_rejected(self):
        page = self.root / 'docs/wiki-src/Home.md'
        page.write_text('{{file:../secret}}\n')
        with self.assertRaisesRegex(wiki.WikiError, 'Unsafe repository path'):
            wiki.build_outputs(self.root)
        page.write_text('[Code](https://github.com/old/repository/blob/main/File.lean)\n')
        with self.assertRaisesRegex(wiki.WikiError, 'use file/lean macros'):
            wiki.build_outputs(self.root)

    def test_pdf_hash_and_short_links_follow_repository_and_ref(self):
        pdf_path = self.root / 'papers/Main paper.pdf'
        pdf_path.parent.mkdir()
        data = b'%PDF-1.4\nA small test fixture.\n'
        pdf_path.write_bytes(data)
        config_path = self.root / 'docs/catalogue/papers.json'
        config = json.loads(config_path.read_text())
        config['papers'][0].update(pdf='papers/Main paper.pdf',
                                    pdf_sha256=hashlib.sha256(data).hexdigest())
        self.write_json('docs/catalogue/papers.json', config)
        home = self.root / 'docs/wiki-src/Home.md'
        home.write_text(home.read_text() + '\n{{pdf:main}}\n')
        outputs = wiki.build_outputs(self.root)
        self.assertIn('[PDF](https://github.com/owner/formalization/blob/main/papers/Main%20paper.pdf)',
                      outputs[Path('docs/wiki/Home.md')])
        relocated = wiki.build_outputs(self.root, 'another/clean-repo', 'v1.0')
        self.assertIn('[PDF](https://github.com/another/clean-repo/blob/v1.0/papers/Main%20paper.pdf)',
                      relocated[Path('docs/wiki/Home.md')])
        pdf_path.write_bytes(data + b'Changed bytes.\n')
        with self.assertRaisesRegex(wiki.WikiError, 'PDF SHA-256 mismatch'):
            wiki.build_outputs(self.root)
        pdf_path.unlink()
        with self.assertRaisesRegex(wiki.WikiError, 'Missing repository file'):
            wiki.build_outputs(self.root)
        del config['papers'][0]['pdf_sha256']
        self.write_json('docs/catalogue/papers.json', config)
        with self.assertRaisesRegex(wiki.WikiError, 'needs a PDF path'):
            wiki.build_outputs(self.root)

    def test_reverse_module_index_deduplicates_statement_per_defining_file(self):
        (self.root / 'Hypertournaments/Core.lean').write_text(
            'namespace Hypertournaments.Native\n'
            'theorem result : True := by trivial\n'
            'theorem other : True := by trivial\n'
            'end Hypertournaments.Native\n')
        self.entry['declarations'].append({'name': 'Hypertournaments.Native.other',
                                           'module': 'Hypertournaments.Core'})
        helper = dict(self.entry, id='main-helper', label=None, title='A helper',
                      declarations=[self.entry['declarations'][0]])
        self.write_entries([self.entry, helper])
        (self.root / 'docs/wiki-src/Lean-file-index.md').write_text(
            '# Defining-file correspondence\n\n{{module-index}}\n')
        outputs = wiki.build_outputs(self.root)
        page = outputs[Path('docs/wiki/Lean-file-index.md')]
        self.assertEqual(page.count('| [`Hypertournaments/Core.lean`]'), 1)
        self.assertEqual(page.count('/wiki/Main-article#main-theorem'), 1)
        self.assertEqual(page.count('/wiki/Main-article#main-helper'), 1)
        self.assertEqual(outputs[Path('docs/CheckTheoremMap.lean')].count(
            '#check Hypertournaments.Native.result'), 1)
        relocated = wiki.build_outputs(self.root, 'another/clean-repo', 'v1.0')
        other_page = relocated[Path('docs/wiki/Lean-file-index.md')]
        self.assertIn('https://github.com/another/clean-repo/wiki/Main-article#main-theorem', other_page)
        self.assertNotIn('owner/formalization', other_page)

    def test_documentation_examples_have_the_same_proof_token_guard(self):
        example = self.root / 'docs/Examples.lean'
        example.write_text('import Hypertournaments\n-- sorry is mentioned only in a comment\n')
        wiki.build_outputs(self.root)
        example.write_text('import Hypertournaments\nexample : False := by sorry\n')
        with self.assertRaisesRegex(wiki.WikiError, 'docs/Examples.lean: forbidden proof token'):
            wiki.build_outputs(self.root)
        example.write_text('import Hypertournaments\naxiom falseClaim : False\n')
        with self.assertRaisesRegex(wiki.WikiError, 'forbidden proof token: axiom'):
            wiki.build_outputs(self.root)
        with self.assertRaisesRegex(wiki.WikiError, 'generated.*forbidden proof token'):
            wiki.check_documentation_lean(self.root, 'axiom bogus : False\n')

    def test_vendor_paths_are_inside_the_same_repository(self):
        relative = 'vendor/ramsey-transfer/CCO/Native.lean'
        source = self.root / relative
        source.parent.mkdir(parents=True)
        source.write_text('namespace CCO\ntheorem result : True := by trivial\nend CCO\n')
        location = wiki.declaration_location(self.root, 'CCO.result', 'CCO.Native')
        self.assertEqual(location['path'], relative)
        self.assertEqual(location['line'], 2)


if __name__ == '__main__':
    unittest.main()
