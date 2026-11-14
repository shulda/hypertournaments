# Independent review: circular encoding and cuts

Reviewer: root agent, independent of the author of the two modules.
Source: `shulda/tex_hypertournaments` at
`919349e7eceed3c7fa0ed126a337c6fae6624704`, cyclic-order cases in the
classification and the discussion following `cor:even-no-eppa`.

## Frozen inputs

| File | SHA-256 |
| --- | --- |
| `Hypertournaments/CircularHyper.lean` | `7e4c5bfa3975c2f692a96fd0b6761bcf625b0d20f642cde4524b4a7c7e39ed80` |
| `Hypertournaments/CircularCut.lean` | `2ba34f8d54d12977b2e11d875bbf32028fa47cfef3547849b3d6dc580e493ff2` |

## Mathematical checks

The constructor uses the existing Mathlib `CircularOrder`, with the
strict circular relation corresponding exactly to orientation `false`.
On injective triples, each of the three transpositions negates that
relation. The proof checks every pair of distinct coordinates, so it gives
an actual `Hyper 3`, not just an unoriented ternary relation.

Compatibility is defined on every injective triple, and its equivalence
with equality to the constructed `Hyper` recovers all Boolean orientations.
`IsCyclicOrder` existentially hides the presentation. The embedding iff
uses the original `Preserves` relation and reflects, as well as preserves,
strict circular betweenness on distinct triples. The reverse direction
uses that a Boolean is determined by whether it equals `false`.

The cut is defined on the entire carrier, with the root least:
`x < y` iff `(x = p and y != p) or sbtw p x y`. Its strict total order
proof treats equality with the root explicitly. Circularizing this order
recovers the original strict relation on **all** triples, including repeated
vertices. The forward direction considers possible relative positions in
the cut; inconsistent orders contradict circular asymmetry. The reverse
direction follows from the three cyclic versions of the increasing case.

The monotonicity theorem retains the original injection and uses only its
root image and its actual preservation of circular triples. It assumes
neither finiteness nor surjectivity. Thus empty/small carriers are covered
by the general definitions; a cut needs exactly its explicit root argument.
No finite representation theorem or rotation-group assumption is hidden
in the circularization step.

## Independent verification

Rebuilt `Hypertournaments.CircularCut` successfully: 924 jobs. Printed
axioms of the constructor, embedding iff, cut order, full reconstruction,
and cut-monotonicity theorem. All prints use only `propext`,
`Classical.choice`, and `Quot.sound`. The frozen source hashes were checked.

No mathematical or interface gap was found. The package receipt additionally
records complete source coverage, the full kernel build, and defining-module
axiom audits.
