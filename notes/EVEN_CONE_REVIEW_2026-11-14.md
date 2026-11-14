# Independent even-cone review — 2026-11-14

Reviewed `Hypertournaments/EvenCone.lean` and
`Hypertournaments/ConeNaturality.lean`, with the tuple/link API in
`Hypertournaments/OnePointLink.lean` inspected as a dependency. The review
found no mathematical gap. The only requested changes were direct tactic
imports (`Mathlib.Tactic.Ext` and `Mathlib.Tactic.Choose`); the author added
them without proof changes, and the final snapshots were rebuilt below.

The source is article commit
`919349e7eceed3c7fa0ed126a337c6fae6624704`,
`prop:even-eppa-transfer`, and its preparation proof of the even cone used
in transfer one arity down. This review covers the cone and its embedding
naturality, rather than the separate EPPA-witness transfer implementation.

## Statements and source alignment

For any even lower arity `r`, the construction gives an even
`(r + 1)`-hypertournament on `Option V`. Its two defining equations are
proved on actual injective tuples:

* `Hyper.evenCone_root_orient` identifies every root-first tuple with the
  original lower orientation.
* `Hyper.evenCone_old_orient` identifies every tuple of old vertices with
  the intrinsic coboundary of the lower orientation.

The ordinal implementation chooses a potential which is zero on subsets
containing the new least vertex and agrees with the old canonical signs
on subsets of old vertices. Its coboundary is even by the existing
intrinsic coboundary theorem. On a root-first increasing tuple, only the
facet omitting the root contributes. The passage from increasing to all
ordered tuples uses `orientations_equal_of_canonical` for the actual
one-point slice. Thus the final equations have no restriction to
increasing tuples and no assumption that embeddings preserve an order.

The arbitrary finite-carrier construction transports through explicit
equivalences `finiteConeIndex` and `optionConeIndex`. The latter maps
`none` to the new least vertex and `some x` to the successor of the old
index. Both defining equations cancel the enumeration explicitly. No
chosen order appears in their statements.

## Naturality and hypotheses

`preserves_option_of_old_and_root` applies to arbitrary upper
hypertournaments and an arbitrary injection of the lower carriers. It
requires neither finiteness nor an order. Every tuple either avoids the
root and factors through `some`, or contains the root in a unique
position. In the second case, swapping that position with the first
reduces to a root-first tuple; the identical permutation sign on both
sides is cancelled. The case where the root is already first is included.

`Hyper.evenCone_preserves` then extends every lower orientation-preserving
embedding `e` by `Function.Embedding.optionMap e`. The old-tuple branch
uses intrinsic coboundary naturality, and the root-first branch uses the
given preservation hypothesis. The map is an injection and fixes the
root. It need not respect either of the arbitrary enumerations used to
construct the two cones.

The `Finite` assumptions on both carriers belong to the cone construction
only. The statements introduce no `Nonempty`, minimum-cardinality,
`r >= 2`, or residue-class assumption beyond `Even r`.

## Edge cases

* At `r = 0`, the root calculation includes the empty sum in
  `Fin.sum_univ_succ`. It recovers the possibly nonzero orientation on the
  unique empty lower tuple as the orientation of the actual root unary
  tuple.
* The old carrier may be empty. In particular, an empty carrier in arity
  zero produces a singleton cone whose root equation is nonvacuous.
  The cone is also defined and even for an empty carrier in positive
  even arity.
* If a carrier is smaller than a relevant positive tuple arity, the
  corresponding universally quantified tuple equation is vacuous; the
  cone and evenness theorem remain unconditional.
* The link dependency prepends a distinguished point to actual tuples.
  Its lifted coordinate permutation fixes that point and has the same
  sign as the lower permutation. No order or upper evenness is used in
  constructing the intrinsic one-point slice.

## Independent verification

On the final source snapshots, using Lean 4.34.1 and the committed Lake
manifest:

```
lake build Hypertournaments.ConeNaturality
lake env lean ../preparation/even-cone-review.lean
```

The build passed (1637 jobs). The separate review file checked arity-zero
evenness on the empty old carrier, its nonvacuous root equation,
arity-two evenness on the empty old carrier, and naturality for an
arbitrary permutation of a three-element old carrier. All examples
elaborated successfully. Local evidence is in
`../preparation/even-cone-independent-build.log` and
`../preparation/even-cone-independent-review.log`.

Each of these selected endpoints reports exactly
`[propext, Classical.choice, Quot.sound]` under `#print axioms`:

* `Hyper.evenConeFin_root_orient`
* `Hyper.evenConeFin_old`
* `Hyper.evenCone_isEven`
* `Hyper.evenCone_root_orient`
* `Hyper.evenCone_old_orient`
* `preserves_option_of_old_and_root`
* `Hyper.evenCone_preserves`

This is a targeted independent review. Facade closure, complete defining
module axiom auditing, and proposed-commit CI remain integration checks.

## Final reviewed SHA-256

| File | SHA-256 |
| --- | --- |
| `Hypertournaments/EvenCone.lean` | `a67f23984b1699d9e4041a743eb23f39e515d2cca8931b4c1fba0a1a1df04102` |
| `Hypertournaments/ConeNaturality.lean` | `953b984511344aa5513f0c1a32774b586f1e5c0e4d35522062b830e52985b54c` |
