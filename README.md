# Formalization of constrained hypertournaments

Lean 4 / Mathlib proofs for finite alternating-orientation hypertournaments.
The negative necessary condition for ordinary amalgamation of `(n+1)`-constrained
classes is proved in every arity `n >= 4`, without an exceptional-family premise.
The main-paper development now also proves strong amalgamation for omission
classes of any family of finite pair-cancelling structures. Their free
linear-order expansions are also proved Ramsey in every arity `n >= 3`.

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

The next main-paper work is the ordering property, followed by potentials
and non-EPPA results. Instantiating
the positive constrained classification still requires the local-type
pair-cancellation cutoff and the switching/potential SAP construction.
Arity-two/three side results remain separate tasks. The five-constrained
ternary classification is postponed.
