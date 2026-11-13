# Formalization of constrained hypertournaments

Lean 4 / Mathlib proofs for finite alternating-orientation hypertournaments.
The current milestone is the negative necessary condition for ordinary
amalgamation of `(n+1)`-constrained classes in every arity `n >= 4`.
The public theorem has no remaining exceptional-family premise.

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

## Build and validation

Use the committed `lean-toolchain` (Lean 4.34.1) and `lake-manifest.json`.

```sh
python3 tools/project_sources.py
lake exe cache get $(python3 tools/project_sources.py --mathlib-roots)
lake --rehash build
lake env lean Hypertournaments/AxiomAudit.lean
```

CI checks the actual proposed head, complete facade coverage, the kernel
build, and every project declaration transitively with the pinned
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

The main-paper formalization will extend the shared orientation, embedding,
local-type and cochain APIs with positive amalgamation, Ramsey expansions,
potentials and non-EPPA results. The positive classification direction and
arity-two/three side results are separate tasks. The five-constrained
ternary classification is postponed.
