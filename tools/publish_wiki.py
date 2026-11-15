#!/usr/bin/env python3
"""Publish the checked documentation pages to the repository's GitHub Wiki.

Run after `wiki_docs.py check` and the Lean checks. Authentication is provided
by Git (in CI, `gh auth setup-git` uses the job's GITHUB_TOKEN). No token is
accepted on the command line or embedded in a remote URL.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

from wiki_docs import WikiError, build_outputs, read_json, write_or_check


def git(directory: Path, *arguments: str) -> str:
    return subprocess.check_output(
        ['git', '-C', str(directory), *arguments], text=True).strip()


def copy_pages(root: Path, destination: Path) -> list[str]:
    pages = sorted((root / 'docs/wiki').glob('*.md'))
    if not any(page.name == 'Home.md' for page in pages):
        raise WikiError('Generated Wiki has no Home.md')
    for page in pages:
        shutil.copyfile(page, destination / page.name)
    return [page.name for page in pages]


def publish(root: Path, repository: str | None, dry_run: bool) -> dict:
    config = read_json(root / 'docs/catalogue/papers.json')
    configured = config.get('repository')
    aliases = config.get('publication_repositories', [])
    if not isinstance(aliases, list) or any(
            not isinstance(alias, str)
            or not re.fullmatch(r'[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+', alias)
            for alias in aliases):
        raise WikiError('publication_repositories must be a list of GitHub owner/repository names')
    destination = repository if repository is not None else configured
    if destination not in [configured, *aliases]:
        raise WikiError(
            'Wiki destination differs from docs/catalogue/papers.json; '
            'configure its repository or publication_repositories first')
    outputs = build_outputs(root)
    write_or_check(root, outputs, check=True)
    revision = git(root, 'rev-parse', 'HEAD')
    with tempfile.TemporaryDirectory(prefix='hypertournaments-wiki-') as temporary:
        target = Path(temporary) / 'wiki'
        subprocess.run(['git', 'clone', '--quiet',
                        f'https://github.com/{destination}.wiki.git', str(target)], check=True)
        branch = git(target, 'symbolic-ref', '--short', 'HEAD')
        names = copy_pages(root, target)
        subprocess.run(['git', '-C', str(target), 'add', '--', *names], check=True)
        changed = bool(git(target, 'diff', '--cached', '--name-only'))
        result = {'repository': destination, 'source_revision': revision,
                  'pages': len(names), 'changed': changed, 'dry_run': dry_run}
        if dry_run or not changed:
            return result
        subprocess.run([
            'git', '-C', str(target), '-c', 'user.name=github-actions[bot]',
            '-c', 'user.email=41898282+github-actions[bot]@users.noreply.github.com',
            'commit', '--quiet', '-m', f'Publish research Wiki from {revision}'
        ], check=True)
        subprocess.run(['git', '-C', str(target), 'push', 'origin', f'HEAD:{branch}'], check=True)
        result['wiki_commit'] = git(target, 'rev-parse', 'HEAD')
        return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repository', help='GitHub publication target; must be configured in the catalogue')
    parser.add_argument('--dry-run', action='store_true', help='Compare with the live Wiki without committing or pushing')
    args = parser.parse_args()
    try:
        result = publish(Path(__file__).resolve().parents[1], args.repository, args.dry_run)
    except (WikiError, subprocess.CalledProcessError) as exc:
        raise SystemExit(f'Wiki publication failed: {exc}') from exc
    print(json.dumps(result))


if __name__ == '__main__':
    main()
