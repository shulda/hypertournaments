#!/usr/bin/env python3
"""Check facade coverage and the pinned vendor snapshot, or list Mathlib cache roots."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import tomllib

VENDOR_DIRECTORY = Path('vendor/ramsey-transfer')
VENDOR_COMMIT = '48a6f3d8bf02bb0dfeb30f69bec8e9d0afa764e6'
VENDOR_SOURCE_DIGEST = 'ae194b3154e25d52e71523b0b8eae966acb6f5c851dc94e2aed9c52ef1ab3422'
VENDOR_PREFIXES = ('CCO.', 'PartiteConstruction.', 'SuccessorTree.')
VENDOR_ENTRYPOINTS = ('CCO.UnaryHN.IteratedTransfer', 'CCO.UnaryHN.OrderedAmbient')
IMPORT_LINE = re.compile(r'^\s*(?:public\s+)?import\s+([A-Za-z0-9_.]+)\s*$', re.M)
RAW_STRING_START = re.compile(r'r(#{0,})"')
CHAR_LITERAL = re.compile(r"'(?:[^'\\\n]|\\(?:u\{[0-9a-fA-F]+\}|u[0-9a-fA-F]{4}|x[0-9a-fA-F]{2}|.))'")


def lean_code(text: str) -> str:
    # Ignore nested Lean comments and string contents, including import examples
    # in documentation; retain newlines so actual header commands stay anchored.
    code = []
    depth = 0
    quoted = False
    raw_end = None
    index = 0
    while index < len(text):
        char = text[index]
        pair = text[index:index + 2]
        if depth:
            if pair == '/-':
                depth += 1
                code.append('  ')
                index += 2
                continue
            if pair == '-/':
                depth -= 1
                code.append('  ')
                index += 2
                continue
            code.append('\n' if char == '\n' else ' ')
        elif raw_end is not None:
            if text.startswith(raw_end, index):
                code.append(' ' * len(raw_end))
                index += len(raw_end)
                raw_end = None
                continue
            code.append('\n' if char == '\n' else ' ')
        elif quoted:
            if char == '\\':
                code.append(' ')
                if index + 1 < len(text):
                    code.append('\n' if text[index + 1] == '\n' else ' ')
                index += 2
                continue
            if char == '"':
                quoted = False
            code.append('\n' if char == '\n' else ' ')
        elif pair == '/-':
            depth = 1
            code.append('  ')
            index += 2
            continue
        elif pair == '--':
            newline = text.find('\n', index)
            if newline == -1:
                break
            code.append(' ' * (newline - index))
            index = newline
            continue
        elif char == 'r' and (index == 0 or not re.match(r"[\w']", text[index - 1])) and (match := RAW_STRING_START.match(text, index)):
            raw_end = '"' + match.group(1)
            code.append(' ' * (match.end() - index))
            index = match.end()
            continue
        elif char == "'" and (index == 0 or not re.match(r"[\w']", text[index - 1])) and (match := CHAR_LITERAL.match(text, index)):
            code.append(' ' * (match.end() - index))
            index = match.end()
            continue
        elif char == '"':
            quoted = True
            code.append(' ')
        else:
            code.append(char)
        index += 1
    return ''.join(code)


def proof_placeholders(text: str) -> list[tuple[int, str]]:
    """Find forbidden code tokens, ignoring prose and quoted examples."""
    clean = lean_code(text)
    return [(clean.count('\n', 0, match.start()) + 1, match.group())
            for match in re.finditer(r"(?<![\w'])(?:sorry|admit|axiom)(?![\w'])", clean)]


def check_proofs(path: Path) -> None:
    findings = proof_placeholders(path.read_text())
    if findings:
        raise SystemExit('\n'.join(f'{path}:{line}: forbidden proof token {token}'
                                   for line, token in findings))


def source_imports(text: str) -> list[str]:
    clean = lean_code(text)
    modules = IMPORT_LINE.findall(clean)
    import_commands = re.findall(r'^\s*(?:public\s+)?import\b[^\n]*', clean, re.M)
    if len(modules) != len(import_commands):
        raise SystemExit('Use one module per import command in receiving/vendor source')
    return modules


def checked_imports(module: str, path: Path) -> list[str]:
    if module == 'Hypertournaments' or module.startswith('Hypertournaments.'):
        check_proofs(path)
    modules = source_imports(path.read_text())
    if any(m in {'Mathlib', 'Mathlib.Tactic'} for m in modules):
        raise SystemExit(f'Broad Mathlib import in {path}')
    if module != 'Hypertournaments' and 'Hypertournaments' in modules:
        if module != 'Hypertournaments.AxiomAudit':
            raise SystemExit(f'Internal module imports the facade: {module}')
    return modules


def snapshot_file(folder: Path, entry: dict) -> bytes:
    relative = Path(entry['path'])
    if relative.is_absolute() or '..' in relative.parts:
        raise SystemExit(f'Invalid vendor path: {relative}')
    path = folder / relative
    if not path.is_file():
        raise SystemExit(f'Missing pinned vendor file: {relative}')
    data = path.read_bytes()
    sha256 = hashlib.sha256(data).hexdigest()
    blob = hashlib.sha1(f'blob {len(data)}\0'.encode() + data).hexdigest()
    if len(data) != entry['bytes'] or sha256 != entry['sha256'] or blob != entry['git_blob_sha1']:
        raise SystemExit(f'Pinned vendor bytes changed: {relative}')
    return data


def vendor_snapshot(root: Path) -> tuple[dict[str, list[str]], dict]:
    folder = root / VENDOR_DIRECTORY
    manifest = json.loads((folder / 'SOURCE_MANIFEST.json').read_text())
    if manifest['commit'] != VENDOR_COMMIT or tuple(manifest['entrypoints']) != VENDOR_ENTRYPOINTS:
        raise SystemExit('Unexpected Ramsey vendor source pin or entry points')
    entries = manifest['files']
    expected = {entry['path'] for entry in entries}
    actual = {str(path.relative_to(folder)) for path in folder.rglob('*.lean')}
    if actual != expected:
        raise SystemExit(f'Vendor source inventory differs: missing={sorted(expected-actual)}, extra={sorted(actual-expected)}')
    modules = {}
    for entry in entries:
        module = entry['module']
        if not module.startswith(VENDOR_PREFIXES) or entry['path'] != module.replace('.', '/') + '.lean':
            raise SystemExit(f'Unexpected vendor module: {module}')
        data = snapshot_file(folder, entry)
        imports = checked_imports(module, folder / entry['path'])
        if imports != entry['imports']:
            raise SystemExit(f'Vendor import manifest differs: {module}')
        if module in modules:
            raise SystemExit(f'Duplicate vendor module: {module}')
        modules[module] = imports
    for entry in manifest['provenance_files']:
        snapshot_file(folder, entry)
    lines = ''.join(f"{entry['sha256']}  {entry['path']}\n" for entry in sorted(entries, key=lambda e: e['path']))
    digest = hashlib.sha256(lines.encode()).hexdigest()
    if digest != VENDOR_SOURCE_DIGEST or manifest['source_digest_sha256'] != digest:
        raise SystemExit('Pinned vendor aggregate source digest differs')
    if manifest['module_count'] != len(modules) or manifest['source_bytes'] != sum(e['bytes'] for e in entries):
        raise SystemExit('Vendor source count or size differs')
    closure = import_closure(modules, VENDOR_ENTRYPOINTS)
    if closure != set(modules):
        raise SystemExit('Vendor snapshot is not exactly the declared import closure')
    config = tomllib.loads((root / 'lakefile.toml').read_text())
    libraries = {lib['name']: lib for lib in config['lean_lib']}
    for name, expected_options in manifest['library_options'].items():
        lib = libraries.get(name)
        if lib is None or lib.get('srcDir') != str(VENDOR_DIRECTORY):
            raise SystemExit(f'Missing pinned vendor library: {name}')
        effective = config.get('leanOptions', {}) | lib.get('leanOptions', {})
        if any(effective.get(k) != v for k, v in expected_options.items()):
            raise SystemExit(f'Receiving compiler options differ for {name}')
    return modules, {'modules': len(modules), 'commit': VENDOR_COMMIT,
                     'source_sha256': digest, 'coverage': 'exact pinned import closure'}


def import_closure(imports: dict[str, list[str]], roots) -> set[str]:
    seen = set()
    todo = list(roots)
    while todo:
        module = todo.pop()
        if module in seen:
            continue
        if module not in imports:
            raise SystemExit(f'Unknown local module: {module}')
        seen.add(module)
        for dependency in imports[module]:
            if dependency.startswith(('Hypertournaments.', *VENDOR_PREFIXES)) or dependency == 'Hypertournaments':
                if dependency not in imports:
                    raise SystemExit(f'Missing imported local module: {dependency} (from {module})')
                todo.append(dependency)
    return seen


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--mathlib-roots', action='store_true')
    mode.add_argument('--vendor-mathlib-roots', action='store_true')
    mode.add_argument('--vendor-only', action='store_true')
    mode.add_argument('--proofs-only', action='store_true')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    paths = [root / 'Hypertournaments.lean', *sorted((root / 'Hypertournaments').rglob('*.lean'))]
    if args.proofs_only:
        for path in paths:
            check_proofs(path)
        print(json.dumps({'modules': len(paths), 'forbidden_proof_tokens': []}))
        return
    vendor_imports, vendor_report = vendor_snapshot(root)
    if args.vendor_only:
        print(json.dumps(vendor_report, indent=2))
        return
    if args.vendor_mathlib_roots:
        closure = import_closure(vendor_imports, VENDOR_ENTRYPOINTS)
        external = sorted({dep for module in closure for dep in vendor_imports[module]
                           if dep.startswith('Mathlib.')})
        print('\n'.join(external))
        return
    imports = {}
    for path in paths:
        module = '.'.join(path.relative_to(root).with_suffix('').parts)
        imports[module] = checked_imports(module, path)
    project_modules = set(imports)
    imports.update(vendor_imports)
    facade = import_closure(imports, ['Hypertournaments'])
    # All own modules include the separately checked readable audit. Traversing
    # their vendor dependencies is essential: direct-only scanning misses HN roots.
    cache_closure = import_closure(imports, project_modules)
    external = sorted({dep for module in cache_closure for dep in imports[module] if dep.startswith('Mathlib.')})
    if args.mathlib_roots:
        print('\n'.join(external))
        return
    excluded = {'Hypertournaments.AxiomAudit'}
    missing = sorted(project_modules - facade - excluded)
    if missing:
        raise SystemExit('Modules missing from the audited facade: ' + ', '.join(missing))
    print(json.dumps({'project_modules': len(project_modules),
                      'facade_modules': len(facade & project_modules),
                      'vendor_modules_in_facade': len(facade & set(vendor_imports)),
                      'external_mathlib_roots': len(external), 'coverage': 'complete',
                      'separately_checked': sorted(excluded), 'vendor': vendor_report}, indent=2))


if __name__ == '__main__':
    main()
