# Formalization of constrained hypertournaments

Lean 4 / Mathlib proofs for finite alternating-orientation hypertournaments.
The negative necessary condition for ordinary amalgamation of `(n+1)`-constrained
classes is proved in every arity `n >= 4`, without an exceptional-family premise.
The main-paper development now also proves strong amalgamation for omission
classes of any family of finite pair-cancelling structures. Their free
linear-order expansions are proved Ramsey and have the ordering property in
every arity `n >= 3`. The development also covers intrinsic even orientations,
their potentials and switching amalgamation.

For `q = (n+1)/2`, a well-formed allowed set `S` containing the central type
can have ordinary AP only if the next-to-central type belongs to `S`, or
`n` is odd and `S` is exactly the switching parity family.
Embeddings are arbitrary vertex injections preserving orientations; the two
new vertices of an amalgam are allowed to be identified. No auxiliary order
is part of a `Hyper` structure or its embeddings.

## Public interface

[`Hypertournaments/NegativeClassification.lean`](Hypertournaments/NegativeClassification.lean)
exports:

```lean
theorem negative_classification
    (n : ℕ) (hn : 4 ≤ n)
    (S : Set ℕ) (hvalid : ValidTypes n S)
    (hcentral : centralIndex n ∈ S)
    (hAP : HasAP n S) : NecessaryAlternatives n S
```

`not_hasAP_of_excluded_types` gives the ordinary non-AP contrapositive.
The underlying proof constructs actual bad one-point spans and excludes
both fresh-vertex identification and distinct-vertex amalgamation.
Central membership is an explicit premise; the separate equivalence with
unboundedness is not supplied through an unformalized Ramsey assumption.

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

Remaining main-paper work includes the finite-group/EPPA arguments and
related consequences. The
positive constrained classification still requires the local-type
pair-cancellation cutoff; switching amalgamation is proved. Other arity-two/three
side results remain separate tasks. The five-constrained
ternary classification is postponed.
