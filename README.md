# Formalization of constrained hypertournaments

Lean 4 / Mathlib proofs for finite alternating-orientation hypertournaments.
Ordinary amalgamation of unbounded `(n+1)`-constrained classes is classified
in every arity `n >= 4`: both the positive and negative directions are proved.
The main-paper development now also proves strong amalgamation for omission
classes of any family of finite pair-cancelling structures. Their free
linear-order expansions are proved Ramsey and have the ordering property in
every arity `n >= 3`. The development also covers intrinsic even orientations,
their potentials and switching amalgamation.

For `n ≥ 4` and `q = (n+1)/2`, a well-formed allowed set `S` containing the central type
has ordinary AP exactly when the next-to-central type belongs to `S`, or
`n` is odd and `S` is exactly the switching parity family.
Embeddings are arbitrary vertex injections preserving orientations; the two
new vertices of an amalgam are allowed to be identified. No auxiliary order
is part of a `Hyper` structure or its embeddings.

## Public interface

[`Hypertournaments/PositiveClassification.lean`](Hypertournaments/PositiveClassification.lean)
exports:

```lean
theorem amalgamation_classification
    (n : ℕ) (hn : 4 ≤ n)
    (S : Set ℕ) (hvalid : ValidTypes n S)
    (hcentral : centralIndex n ∈ S) :
    HasAP n S ↔ NecessaryAlternatives n S
```

Both alternatives have actual strong amalgams on the exact-overlap carrier.
`central_next_ordered_strong_span` also preserves compatible free orders.
`NegativeClassification` retains the necessary condition and ordinary non-AP
contrapositive, including its actual bad one-point spans.

[`Hypertournaments/CentralUnbounded.lean`](Hypertournaments/CentralUnbounded.lean)
proves `UnboundedAdmissible n S ↔ centralIndex n ∈ S` in every arity.
Its finite Ramsey argument uses the already proved theorem for pure linear
orders, with no Ramsey premise about the admissible class.
[`UnboundedClassification`](Hypertournaments/UnboundedClassification.lean)
therefore exports the corresponding exact classification of unbounded classes.

[`LocalTypeIsomorphism`](Hypertournaments/LocalTypeIsomorphism.lean) proves that
local index is a complete isomorphism invariant for n≥2, and
[`LocalTypeRealization`](Hypertournaments/LocalTypeRealization.lean) realizes
every valid index by an actual structure. The exact local PC criterion is
proved in both directions:
on `n+1` vertices, `PairCancelling A` iff its index is at most `q-2` for `n≥3`.
The omission-class bridge uses actual forbidden packets on arbitrary carriers.
[`LocalClassRamsey`](Hypertournaments/LocalClassRamsey.lean) supplies actual
admissible Ramsey and ordering witnesses for the central/next-central branch.

## Main-paper positive amalgamation

[`Hypertournaments/PairAmalgamation.lean`](Hypertournaments/PairAmalgamation.lean)
exports `pair_cancelling_hasStrongAmalgamation`, the arbitrary-finite-carrier
`pair_cancelling_strong_span`, and `pair_cancelling_ordered_strong_span`.
The two carrier injections identify exactly the original base. Empty bases
are allowed; arbitrary source embeddings are retained.

`exists_pair_cancelling_completion` completes a consistent partial orientation
on the same carrier by its last missing pair and proves forbidden-freeness.
The arbitrary-relational completion theorem is now supplied by the
Ramsey adapter below. `preserves_iff_relation` supplies the induced relational encoding,
with relation truth corresponding to orientation `false`.
See the [source and review note](notes/PAIR_CANCELLING_AMALGAMATION_2026-11-13.md)
for precise scope and remaining links to the classification.

## Main-paper Ramsey theorem

[`Hypertournaments/PairRamsey.lean`](Hypertournaments/PairRamsey.lean) exports
`Ramsey.pair_cancelling_ordered_ramsey` and the explicit
`Ramsey.exists_ordered_ramsey_witness`: for any finite ordered inputs in the
omission class and any finite nonempty colour palette, the witness is an
actual finite ordered forbidden-free `Hyper`.

`Ramsey.exists_relational_completion` takes arbitrary R,< structures with
extendible comparisons and valid irreducible pieces. It constructs a completion
on the identical carrier, with the identity a homomorphism-embedding.
The article's pair-coverage definition of irreducibility is proved equivalent
to the library's native definition. HN local finiteness holds with cutoff one.

The existing ambient Ramsey theorem and HN transfer are used from an exact
119-module [pinned source closure](vendor/ramsey-transfer/PROVENANCE.md).
All source bytes and receiving compiler options are checked. See the
[source/review note](notes/PAIR_CANCELLING_RAMSEY_2026-11-13.md).

## Ordering property and potentials

[`Hypertournaments/PairOrdering.lean`](Hypertournaments/PairOrdering.lean)
proves the full ordering property for pair-cancelling omission classes. The
finite target is chosen before both free orders. The unrestricted binary
case is proved separately in
[`Hypertournaments/BinaryOrdering.lean`](Hypertournaments/BinaryOrdering.lean):
two ordered edge types are homogenized separately, and a directed triangle
rules out opposite comparison colours. Unrestricted ordered Ramsey and strong
amalgamation are available uniformly for every arity at least two.

[`Hypertournaments/EvenPotential.lean`](Hypertournaments/EvenPotential.lean)
proves that a finite orientation in odd arity is even exactly when it has an
alternating potential in the preceding even arity. Coboundaries are intrinsic
functions on injective tuples; naturality and `δ² = 0` are proved directly.
The empty carrier is included. Gauge alignment extends a chosen base potential
along an arbitrary vertex embedding while retaining the upper orientation.

[`Hypertournaments/EvenAmalgamation.lean`](Hypertournaments/EvenAmalgamation.lean)
proves strong amalgamation for finite even hypertournaments, with compatible
orders as well. The equivalence with the existing `switchingAllowed` palette
holds for **every odd arity**, and `switching_hasAP` supplies its positive
ordinary-AP theorem in arities at least three.

[`Hypertournaments/PotentialRamsey.lean`](Hypertournaments/PotentialRamsey.lean)
proves Ramsey for the full potential expansions, including the ternary case.
Their native language names the upper orientation, lower potential and free
linear order; all embeddings preserve and reflect all three relations.
[`Hypertournaments/PotentialExpansionProperty.lean`](Hypertournaments/PotentialExpansionProperty.lean)
proves the full expansion property relative to finite even reducts: the
upper witness is fixed before both potentials and both orders are chosen.
See the [source and verification note](notes/ORDERING_AND_POTENTIALS_2026-11-13.md).

## Elementary group theory and EPPA foundations

[`Hypertournaments/KleinCentralizerGeneration.lean`](Hypertournaments/KleinCentralizerGeneration.lean)
proves the article's centralizer-generation theorem for every odd finite group
acted on by a Klein four-group. The proof is elementary: invariant Sylow
subgroups, the finite p-group normalizer condition, and an odd-coset fixed
representative. All restricted and quotient actions are constructed; no
external coprime-generation theorem is assumed. The odd-kernel order-four
quotient lifting theorem is also proved using actual Sylow restriction
isomorphisms.

[`OddStabilizer`](Hypertournaments/OddStabilizer.lean) proves that the actual
pointwise automorphism stabilizer of at least `n-2` vertices has odd order
in every finite n-hypertournament, `n≥2`. [`EPPA`](Hypertournaments/EPPA.lean)
defines ordinary finite witnesses using actual induced partial automorphisms,
proves finite-target reindexing, and connects an unrestricted finite-witness
obstruction to class-level non-EPPA.

See the [classification and group source/review note](notes/CLASSIFICATION_AND_GROUPS_2026-11-14.md)
for exact scope, independent reviews and remaining obligations.

## EPPA obstructions and transfer

[`LocalEPPAObstruction`](Hypertournaments/LocalEPPAObstruction.lean) proves the
actual four-equal-facets local obstruction to every unrestricted finite
EPPA witness. The Klein action is constructed on the full packet and lifted
from ordinary separate EPPA extensions by Sylow; coherence is not assumed.

[`EPPAConsequences`](Hypertournaments/EPPAConsequences.lean) proves:

- every unbounded hereditary SAP class in arity `n≥6` fails EPPA;
- in arity `n≥4`, a hereditary SAP class containing a packet of index
  `d≤n-3` fails EPPA;
- one `n+2`-vertex obstruction works simultaneously for every PC omission
  class in each arity `n≥4`, even against unrestricted finite targets.

[`EPPATransfer`](Hypertournaments/EPPATransfer.lean) proves the one-arity-down
implication for every odd upper arity at least three, using actual rooted
cones and witness links. The upper witness need not be even.
[`EvenNoEPPA`](Hypertournaments/EvenNoEPPA.lean) consequently proves non-EPPA
for even hypertournaments in every odd arity at least five, with the explicit
arity-five corollary. See the [source and review note](notes/HIGH_ARITY_EPPA_2026-11-14.md).

## Build and validation

Use the committed `lean-toolchain` (Lean 4.34.1) and `lake-manifest.json`.

```sh
python3 tools/project_sources.py
lake exe cache get $(python3 tools/project_sources.py --mathlib-roots)
lake --rehash build
lake env lean Hypertournaments/AxiomAudit.lean
```

CI checks the actual proposed head, complete facade coverage, the kernel
build, and every project and vendored declaration transitively with the pinned
`axiom-audit` tool. Its allowlist is `propext,Classical.choice,Quot.sound`.
The JSON audit is a workflow artifact. Selected axiom prints are supplements.
Small Boolean obstructions use kernel-checked propositional LRAT proofs;
regeneration of their certificates does not change the trusted base.
See the [takeover review](notes/TAKEOVER_REVIEW_2026-11-13.md) for the final
source modules, original green CI heads, and integration checks.

## Sources and remaining work

The source negative argument is the AI-written Lean-oriented
[`negative_general_arity_audit_v4.tex`](notes/negative_general_arity_audit_v4.tex).
Source text and kernel-checked Lean statements are distinct artifacts.

Remaining article work includes the finite cyclic-order encoding and its
small-arity SAP/non-EPPA consequences. The infinite pair-cancelling antichain
and Fraisse consequences require their own additional infrastructure.
Five-constrained ternary classification remains postponed.
