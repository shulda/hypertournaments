import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from publish_wiki import copy_pages, publish
from wiki_docs import WikiError


class WikiPublishingTests(unittest.TestCase):
    def test_copy_keeps_other_wiki_pages(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / 'source'
            pages = root / 'docs/wiki'
            pages.mkdir(parents=True)
            (pages / 'Home.md').write_text('new home\n')
            (pages / 'Main-article.md').write_text('theorems\n')
            target = Path(temporary) / 'wiki'
            target.mkdir()
            (target / 'Home.md').write_text('old home\n')
            (target / 'Other.md').write_text('manual page\n')
            self.assertEqual(copy_pages(root, target), ['Home.md', 'Main-article.md'])
            self.assertEqual((target / 'Home.md').read_text(), 'new home\n')
            self.assertEqual((target / 'Other.md').read_text(), 'manual page\n')

    def test_missing_home_is_rejected_before_copying(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / 'docs/wiki').mkdir(parents=True)
            with self.assertRaisesRegex(WikiError, 'no Home'):
                copy_pages(root, root)

    def test_migration_cannot_publish_to_the_wrong_repository(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / 'docs/catalogue').mkdir(parents=True)
            (root / 'docs/catalogue/papers.json').write_text(json.dumps({'repository': 'owner/old'}))
            with self.assertRaisesRegex(WikiError, 'destination differs'):
                publish(root, 'owner/new', dry_run=False)

    def test_configured_alias_is_the_actual_publication_target(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / 'docs/catalogue').mkdir(parents=True)
            (root / 'docs/catalogue/papers.json').write_text(json.dumps({
                'repository': 'owner/canonical',
                'publication_repositories': ['owner/temporary'],
            }))
            with patch('publish_wiki.build_outputs', return_value={}) as build, \
                    patch('publish_wiki.write_or_check') as check, \
                    patch('publish_wiki.git', side_effect=[
                        'source-sha', 'master', 'Home.md', 'wiki-sha']) as git, \
                    patch('publish_wiki.copy_pages', return_value=['Home.md']), \
                    patch('publish_wiki.subprocess.run') as run:
                result = publish(root, 'owner/temporary', dry_run=False)
            build.assert_called_once_with(root)
            check.assert_called_once_with(root, {}, check=True)
            clone = run.call_args_list[0].args[0]
            self.assertEqual(clone[:4], [
                'git', 'clone', '--quiet', 'https://github.com/owner/temporary.wiki.git'])
            self.assertEqual(run.call_args_list[-1].args[0], [
                'git', '-C', clone[4], 'push', 'origin', 'HEAD:master'])
            self.assertEqual(result['repository'], 'owner/temporary')
            self.assertEqual(result['wiki_commit'], 'wiki-sha')
            git.assert_any_call(root, 'rev-parse', 'HEAD')


if __name__ == '__main__':
    unittest.main()
