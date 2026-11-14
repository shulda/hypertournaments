#!/usr/bin/env python3
"""Keep the independently supplied definitions frozen during proof work."""
from pathlib import Path
import difflib
import hashlib
import json

ROOT = Path(__file__).resolve().parents[2]
ORIGINAL = ROOT / 'notes/independent_intro/original/independent_hypertournament_statements.lean.txt'
STATEMENTS = ROOT / 'Hypertournaments/Independent/Statements.lean'
PATCH = ROOT / 'notes/independent_intro/statements.patch'
ORIGINAL_SHA256 = 'c8c94e105065623be472cf0c1f4bc06225d87a324bf360bcebb483f0e32006b2'
COMPILED_SHA256 = 'cb03f5d89c63d400637efda49db18d56aa4e2e5a400edfd8a2492182f9b148fa'


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def main():
    original = ORIGINAL.read_bytes()
    require(hashlib.sha256(original).hexdigest() == ORIGINAL_SHA256,
            'Uploaded statements changed')
    old = b'import Mathlib\n'
    new = (b'import Mathlib.Data.ZMod.Basic\n'
           b'import Mathlib.Algebra.BigOperators.Group.Finset.Defs\n')
    require(original.startswith(old), 'Unexpected original import header')
    expected = new + original[len(old):]
    require(STATEMENTS.read_bytes() == expected, 'Independent definitions or targets changed')
    require(hashlib.sha256(expected).hexdigest() == COMPILED_SHA256,
            'Unexpected compiled statement hash')
    patch = ''.join(difflib.unified_diff(
        original.decode().splitlines(keepends=True), expected.decode().splitlines(keepends=True),
        fromfile='uploaded/independent_hypertournament_statements.lean',
        tofile='Hypertournaments/Independent/Statements.lean'))
    require(PATCH.read_text() == patch, 'Recorded mechanical diff changed')
    print(json.dumps({'independent_statements': 'unchanged apart from specific imports',
                      'original_sha256': ORIGINAL_SHA256,
                      'compiled_sha256': COMPILED_SHA256,
                      'mechanical_diff': 'verified'}))


if __name__ == '__main__':
    main()
