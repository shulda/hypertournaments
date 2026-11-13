#!/usr/bin/env python3
"""Check facade coverage or list the actual external Mathlib cache roots."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mathlib-roots', action='store_true')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    paths = [root / 'Hypertournaments.lean', *sorted((root / 'Hypertournaments').rglob('*.lean'))]
    imports = {}
    for path in paths:
        module = '.'.join(path.relative_to(root).with_suffix('').parts)
        modules = re.findall(r'^\s*import\s+([A-Za-z0-9_.]+)\s*$', path.read_text(), re.M)
        if any(m in {'Mathlib', 'Mathlib.Tactic'} for m in modules):
            raise SystemExit(f'Broad Mathlib import in {path.relative_to(root)}')
        if module != 'Hypertournaments' and 'Hypertournaments' in modules:
            if module != 'Hypertournaments.AxiomAudit':
                raise SystemExit(f'Internal module imports the facade: {module}')
        imports[module] = modules
    external = sorted({m for modules in imports.values() for m in modules if m.startswith('Mathlib.')})
    if args.mathlib_roots:
        print('\n'.join(m.replace('.', '/') + '.lean' for m in external))
        return
    seen = set()
    todo = ['Hypertournaments']
    while todo:
        module = todo.pop()
        if module in seen:
            continue
        seen.add(module)
        todo.extend(m for m in imports.get(module, []) if m in imports)
    excluded = {'Hypertournaments.AxiomAudit'}
    missing = sorted(set(imports) - seen - excluded)
    if missing:
        raise SystemExit('Modules missing from the audited facade: ' + ', '.join(missing))
    print(json.dumps({'project_modules': len(imports), 'facade_modules': len(seen),
                      'external_mathlib_roots': len(external), 'coverage': 'complete',
                      'separately_checked': sorted(excluded)}, indent=2))


if __name__ == '__main__':
    main()
