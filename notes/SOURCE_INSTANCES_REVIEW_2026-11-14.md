# Independent source-instance review, 2026-11-14

Reviewed `KleinCentralizerGeneration.lean` and
`UnboundedClassification.lean` against the article at
`919349e7eceed3c7fa0ed126a337c6fae6624704`, respectively
`lem:klein-centralizer-generation` and `thm:constrained-classification`.
The review checks that the generic results have their actual source
instances discharged, rather than leave stronger provider or generator
premises on the article-facing statements.

No blocking mathematical or API issue was found in either wrapper.

## Arbitrary Klein four-group actions

`KleinCentralizerGeneration` assumes the standard `IsKleinFour E` mixin,
an automorphism action `MulDistribMulAction E K`, finiteness of `K`, and
odd cardinality of `K`. A group action in this class acts by genuine
multiplicative automorphisms; neither faithfulness nor commutativity of
the acted-on group is assumed.

Mathlib's `IsKleinFour` requires cardinality four and exponent two. The
private helper chooses two distinct nonidentity elements using that
actual cardinality. Exponent two gives both involution equations, and
the resulting commutativity theorem supplies their commutation. Their
product is nonidentity because the chosen elements are distinct and
self-inverse. The wrappers also derive `IsPGroup 2 E` directly from
`Nat.card E = 4 = 2^2`.

Thus both public results discharge every chosen-involution and p-group
hypothesis of the generic saturation/generation theorem. The source-facing
generation statement is exactly

```
Subgroup.closure {x : K | ∃ e : E, e ≠ 1 ∧ e • x = x} = ⊤
```

for every finite odd-order group with a Klein action. It is not a
conditional theorem requiring users to supply those auxiliary elements
or an `IsPGroup` proof. The saturation wrapper retains exactly its
mathematical subgroup hypotheses: stability under the action and
containment of all nonidentity scalars' fixed elements.

The generic generation proof closes the required stable-subgroup
obligation by transporting a fixed element under a scalar and conjugating
its fixing scalar; subgroup closure is then preserved by the action.
This proves the stability needed by saturation rather than assuming it
for the generated subgroup. No nontriviality hypothesis on `K` is
introduced; the trivial acted-on group is included.

## Unboundedness and the original AP classification

`UnboundedAdmissible n S` means actual arbitrarily large finite
admissible structures:

```
∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧ ∃ A : Hyper n (Fin m), Admissible S A
```

`unbounded_amalgamation_classification` uses the proved
`unboundedAdmissible_iff_central` theorem to obtain central membership
from this hypothesis, then applies the exact ordinary-AP classification.
Its statement requires `n ≥ 4`, validity of the palette, and actual
unboundedness; it has no additional central-membership or Ramsey-provider
premise.

`unbounded_amalgamation_iff` also proves both directions of the combined
statement. Unboundedness supplies central membership and the negative
classification supplies the alternatives in one direction. Central
membership constructs arbitrarily large admissible structures, and the
fully proved positive classification supplies ordinary AP in the other.
The result is exactly

```
(UnboundedAdmissible n S ∧ HasAP n S) ↔
  (centralIndex n ∈ S ∧ NecessaryAlternatives n S)
```

with the shared original `HasAP` and source alternatives. `ValidTypes`
remains explicit, as required by the exact switching-palette equality;
phantom indices are not silently treated as literal members of that
palette. This wrapper does not replace ordinary AP by an ordered or
stronger surrogate.

`CentralUnbounded` itself is subject to a separate independent review.
For this wrapper audit its exact proved interface was checked: the bridge
requires neither AP nor validity nor a Ramsey hypothesis about the
admissible class. Its pure-order finite Ramsey input is an actual proved
dependency, rather than an assumption exposed by these source instances.

## Verification and frozen snapshots

An independent targeted build of the two wrappers passed with 2037 jobs.
Four selected public export checks all reported exactly `propext`,
`Classical.choice`, and `Quot.sound`. Standalone smoke checks also
instantiated generation with the concrete Klein group
`Multiplicative (ZMod 2 × ZMod 2)` without chosen generators or a p-group
argument, and expanded the combined unbounded/AP iff to the actual
quantifiers and explicit source alternatives.

Local reproduction and evidence:

```
lake build Hypertournaments.KleinCentralizerGeneration \
  Hypertournaments.UnboundedClassification
lake env lean ../preparation/SourceInstancesReviewCheck.lean
```

The logs are `../preparation/evidence/source-instances-independent-build.log`
and `../preparation/evidence/source-instances-independent-exports.log`.
The reviewed frozen snapshots have these SHA-256 hashes:

| Module | SHA-256 |
| --- | --- |
| `KleinCentralizerGeneration.lean` | `9b82e5bf8ab6b8f55b7e903cf462c4f7e54c7710e076db31dd90c032938cc7a5` |
| `UnboundedClassification.lean` | `98951735400a59e97365f237e52eb5cb2da68576404438768b66ef51f16092a3` |
| `CentralUnbounded.lean` (interface dependency) | `83434a8478767118e15b33b602d257763285b43f60a24df4fb41a4082a815df6` |

No proof files were changed for this independent review.

## Local type realization

The subsequently frozen `LocalTypeRealization.lean` was reviewed against
the prepared `lem:local-type-isomorphism`. It realizes arbitrary
normalized Boolean packets as actual intrinsic hypertournaments.

For an `n`-element facet of `Fin (n+1)`, the complement is the singleton
containing its omitted coordinate. `normalizedPacketSigns` prescribes
the corresponding input bit with the deleted-coordinate parity
correction. The shared ordered-sign constructor then extends those
canonical prescriptions to a genuine alternating orientation.
`fromNormalizedPacket_facet` proves the actual raw facet equation, and
`normalizedFacet_fromNormalizedPacket` cancels the parity correction
twice to recover every input bit. Thus all packet coordinates are
independently realized; there is no missing global constraint or mere
sign-table object in the output.

`localTypeRepresentative n d` puts exactly the first `d` normalized bits
equal to true. The positive-count theorem requires `d ≤ n+1`, while the
local-index theorem correctly strengthens that guard to `d ≤ q`, so that
`min d (n+1-d) = d`. `exists_localIndex_eq` therefore realizes every
valid local index with an actual `Hyper n (Fin (n+1))`.

These realization results hold in every arity, including zero and one.
They do not claim that local index classifies isomorphism in those low
arities. The latter requires the separate lower bound described next.

## Actual local isomorphisms and permutation parity

The frozen `LocalTypeIsomorphism.lean`, its
`FacetOrientationRecovery.lean` helper, and the exact sign law in
`NormalizedPacketSign.lean` were also reviewed. No mathematical or API
issue was found.

The main endpoint is precisely

```
localIndex A (Function.Embedding.refl _) =
    localIndex B (Function.Embedding.refl _) ↔
  ∃ σ : Equiv.Perm (Fin (n+1)), Preserves A B σ.toEmbedding
```

for `n ≥ 2`. This is a bijection of the actual vertex sets preserving
every ordered injective `n`-tuple orientation. The permutation need not
preserve the canonical vertex linear order; that order is auxiliary and
is not part of an intrinsic `Hyper`.

Equality of minority counts implies that the two positive counts are
equal or complementary. Matching color classes alone is insufficient:
the normalized packet is globally complemented exactly when the matching
vertex permutation is odd. The proof addresses this by prescribing the
permutation's parity at the same time as matching colors.

Every Boolean packet with at least three entries has a repeated color.
If an initial color-matching permutation has the wrong parity, composing
it with the domain transposition of two equally colored target entries
changes its parity and preserves the coordinate-by-coordinate match.
In the complementary-count case the proof matches the complemented
target and chooses odd parity; in the equal-count case it matches the
original target and chooses even parity. Consequently the global
complement in the exact normalized-facet permutation law cancels in the
required direction.

`preserves_of_normalizedFacets` then cancels each coordinate's
normalization on the actual facets. Every `n`-subset of `Fin (n+1)`
omits exactly one vertex, and its increasing enumeration is literally
that facet. Equality on these facets therefore recovers all ordered
tuples by alternation. This produces full intrinsic `Preserves`, not
just equality of counts or a match of canonical packets. Invariance of
the local index under an actual preserving permutation proves the
reverse implication.

The bound `n ≥ 2` is essential and correctly retained: packet size at
least three supplies the repeated-color parity correction. In unary
arity the two constant unary orientations on two vertices have the same
minority index but are not isomorphic. No low-arity overclaim is made.

The realization and isomorphism packages compose to a genuine normal
form: every packet in arity at least two admits an actual preserving
vertex permutation into `localTypeRepresentative n d`, where `d` is its
own local index. Thus the source's local representatives have both
existence and actual isomorphism classification discharged.

## Additional local-type verification and hashes

Independent targeted builds passed for `LocalTypeRealization` (949 jobs)
and `LocalTypeIsomorphism` (1522 jobs). Four realization export checks and
eight isomorphism/helper export checks reported exactly `propext`,
`Classical.choice`, and `Quot.sound`.

Standalone checks covered realization in arities zero and one, the
isomorphism criterion at its bottom arity two, and the composition into
the actual representative normal form. Local reproduction files are
`../preparation/LocalTypeRealizationReviewCheck.lean` and
`../preparation/LocalTypeIsomorphismReviewCheck.lean`. Their build and
export logs are in `../preparation/evidence/`, with prefixes
`local-type-realization-independent-` and
`local-type-isomorphism-independent-` respectively.

| Module | SHA-256 |
| --- | --- |
| `LocalTypeRealization.lean` | `a5e506693beb92ac331fdd939383da9c3d0155355ba556c4e764a5263b7ca3fc` |
| `FacetOrientationRecovery.lean` | `341ed45d85fc1af58a14d85bfe0d5508f3bf28ac9c18860d5b6697d954988a65` |
| `NormalizedPacketSign.lean` | `6e45d00ad6896202e05293c0769869b16e83d3f0afee4ed9e327cd3b9e5a4de5` |
| `LocalTypeIsomorphism.lean` | `9b25053ecd71ed294f90c0574369b44dfb0d8de0660f1654785d3fc84b63f8ca` |

These additional reviews also changed no proof files and do not concern
the postponed five-constrained ternary classification.
