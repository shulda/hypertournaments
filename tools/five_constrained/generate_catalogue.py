#!/usr/bin/env python3
"""Regenerate/check the two finite catalogue lookup functions (no trusted search code).

The Lean theorems independently prove coverage, recognition and invariance.
This utility is only a reproducible source of the finite literal lookup functions.
"""
import argparse
from itertools import combinations, permutations
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
REPS = [0, 1, 2, 9, 10, 11, 12, 13, 25, 41, 82, 83]
TRIPLES = list(combinations(range(5), 3))
INDEX = {t: i for i, t in enumerate(TRIPLES)}

def generate():
    labels, witnesses = {}, {}
    for label, representative in enumerate(REPS):
        orbit = set()
        for p in permutations(range(5)):
            mask = 0
            for i, triple in enumerate(TRIPLES):
                image = [p[v] for v in triple]
                odd = sum(image[a] > image[b] for a in range(3) for b in range(a+1, 3)) % 2
                mask |= (((representative >> i) & 1) ^ odd) << INDEX[tuple(sorted(image))]
            orbit.add(mask)
            witnesses.setdefault(mask, sum(p[i] * 5**i for i in range(5)))
        assert min(orbit) == representative
        assert not orbit.intersection(labels)
        labels.update({mask: label for mask in orbit})
    assert set(labels) == set(range(1024))
    return [labels[m] for m in range(1024)], [witnesses[m] for m in range(1024)]

def lookup_tree(values, lo=0, level=1):
    if len(values) == 1:
        return str(values[0])
    mid = lo + len(values)//2
    left = lookup_tree(values[:len(values)//2], lo, level+1)
    right = lookup_tree(values[len(values)//2:], mid, level+1)
    if len(values) <= 8:
        return f'if m < {mid} then ({left}) else ({right})'
    indent = '  '*level
    return f'if m < {mid} then\n{indent}  ({left})\n{indent}else\n{indent}  ({right})'

def update(path, name, values, end_marker, check):
    text = path.read_text()
    start = text.index(f'def {name} (m : ℕ)')
    body = text.index(':=\n  ', start) + len(':=\n  ')
    end = text.index(end_marker, body)
    literal = lookup_tree(values) + '\n\n'
    if check:
        assert text[body:end] == literal, (path, 'lookup differs')
    else:
        path.write_text(text[:body] + literal + text[end:])

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    labels, witnesses = generate()
    folder = ROOT / 'Hypertournaments/FiveConstrained'
    update(folder / 'Catalogue.lean', 'type5Lookup', labels, '/-- Isomorphism label', args.check)
    update(folder / 'CatalogueRecognition.lean', 'orbitWitnessCode', witnesses, 'def orbitWitnessMap', args.check)
    print('Catalogue lookups match signed S5 action' if args.check else 'Catalogue lookups regenerated')

if __name__ == '__main__':
    main()
