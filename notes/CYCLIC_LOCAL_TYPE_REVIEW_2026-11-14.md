# Independent cyclic local-type review, 2026-11-14

Source: `shulda/tex_hypertournaments` at
`919349e7eceed3c7fa0ed126a337c6fae6624704`, the cyclic-order case in the
four-constrained ternary classification and the cyclic-order discussion
following `cor:even-no-eppa`. Reviewed frozen `CyclicRelation.lean` and
`CyclicLocalType.lean` against the actual `Hyper`, normalized-facet,
minority-count, and Mathlib `CircularOrder` definitions.

No blocking mathematical or API issue was found. The reviewer did not
modify either reviewed proof file. This review concerns the encoding and
exact local palette; it does not assert the cyclic class's amalgamation,
Ramsey, expansion, or EPPA properties.

## Actual relation and four-point transitivity

`Hyper.cyclicRel` asserts existence of an actual injective ternary tuple
with the specified three vertices and orientation false. The recovery
lemma proves that every such tuple has the same orientation, by equality
of the three-coordinate embeddings. The relation is therefore intrinsic,
not an auxiliary presentation supplied by an unproved hypothesis.

Distinctness follows from injectivity. Cyclicity uses an explicitly
defined three-cycle with sign positive, and reversal uses the actual
outer-coordinate swap and its sign-changing orientation law. Totality
on three different points chooses the actual orientation and reverses
the tuple when necessary.

The normalized facet vector of an arbitrary four-tuple is proved to be
exactly `[raw0, !raw1, raw2, !raw3]`. The central minority count is two.
When `raw0 = raw2 = false`, the remaining two normalized entries must
both be true; in particular `raw1 = false`. The closed Boolean check in
`ternary_packet_trans` is ordinary kernel-checked `decide`, with no
native-decide axiom or external certificate.

For the circular transitivity axiom, the tuple is literally `[a,b,d,c]`.
Its facets zero and two are the two given circular relations, and facet
one is the required conclusion. All six distinctness conditions are
proved. The only additional possible coincidence, `a = d`, contradicts
asymmetry after cyclically rotating the second hypothesis twice. Thus
the four-tuple is genuinely injective; a repeated-point case is not
silently passed to the local admissibility hypothesis.

## Mathlib circular order on the original carrier

`Hyper.cyclicOrder` uses the original strict relation as `sbtw`, and its
weak relation is equality of any pair or the strict circular relation.
This matches Mathlib's convention that every triple with a repeated
vertex satisfies weak betweenness and fails strict betweenness.

The proof of `sbtw_iff_btw_not_btw` handles each repeated-point case
explicitly in both directions. Weak cyclicity permutes all equality
cases correctly. Weak antisymmetry either exhibits the required equality
or contradicts strict asymmetry. Weak totality handles all equality
cases before invoking the proved distinct-point strict totality. The
strict transitivity field is the actual four-point argument above.

No root, cardinality, finiteness, inhabitedness, or classical finite-order
reconstruction is assumed. In particular the construction also applies
to the empty carrier, and local constraints on carriers of fewer than
four vertices are correctly vacuous.

## Converse and the exact palette

For an arbitrary Mathlib circular order and injective four-tuple, the
converse cuts the full carrier at its first vertex. The other three
vertices are proved different from the root. The three rooted facets
are therefore exactly the corresponding comparisons in the cut order;
the fourth facet uses the complete circular-reconstruction formula.

The finite calculation considers all eight comparison choices among
three distinct nonroot vertices. The impossible choices are removed by
linear-order laws; the six actual relative orders each yield precisely
two positive normalized facets. This calculation is made against the
actual minority-count `localIndex`, not an independent surrogate.

`admissible_two_iff_isCyclicOrder` consequently proves the literal
equivalence between `Admissible ({2} : Set Nat)` and existence of a
compatible Mathlib circular order on the same carrier. Its reverse
direction uses the proved equality with `Hyper.ofCircularOrder`, not
merely a relation on a selected set of tuples.

The two exact-palette results correctly require an actual injective
four-tuple. This is necessary: on a carrier with fewer than four vertices,
the local-index range is empty and admissibility holds in every palette.
No such size condition is introduced into the main equivalence.

## Validation and frozen snapshots

An independent two-target build passed (928 jobs). Nine focused axiom
prints, covering packet transitivity, the circular-order construction,
orientation recovery, the converse local count, admissibility, the main
equivalence, and both exact-palette endpoints, all reported exactly
`propext`, `Classical.choice`, and `Quot.sound`.

Additional kernel-checked examples cover arbitrary structures on every
`Fin a` with `a <= 3`, the arbitrary-carrier constructor without a finite
instance, repeated strict and weak triples, an infinite circular carrier
(`Int`), the empty local-index range on three vertices, and the singleton
range on four vertices. The reviewed files contain no `sorry`, `admit`,
custom axiom, `native_decide`, or unsafe declaration.

Evidence: `../preparation/cyclic-local-independent-build.log`,
`../preparation/cyclic-local-independent-check.lean`, and
`../preparation/cyclic-local-independent-axioms.log`.

| Module | SHA-256 |
| --- | --- |
| `CyclicRelation.lean` | `cfb25df5d256de03f094fb8d642307827bc36007b765b7e07cc146f2601ab906` |
| `CyclicLocalType.lean` | `4dd75cdf94af2cb4a81e0c0286f0e84dbbc43898a27092f8197bb4130bf70f3b` |
