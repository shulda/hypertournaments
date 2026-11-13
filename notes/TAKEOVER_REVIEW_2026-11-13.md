# Work takeover and final negative-classification review

The user confirmed that the former Chat conversation had ended and authorized
this Work project to continue. Codex performed this review after that handover.
There is no concurrent-writer queue to maintain.

## Exact incoming checkpoints

- Working branch `formalization/general-negative-bootstrap`:
  `d39ce1e25edfe52ed0085b7c96ecd323288057fc`, green CI `43467752829`.
- Final stacked p3 candidate, PR 408:
  `2196935906212c9c41479d09268b9413bafb0158`, green CI `43467560377`.
- Identification bridge separately staged in PR 409:
  `bd5defdf4bdb56db341ba53a27c6972a0164d845`, green CI `43467965491`.
- Mathematical source: `negative_general_arity_audit_v4.tex` in this directory.
- Main-paper preparation source: private `shulda/tex_hypertournaments`
  commit `919349e7eceed3c7fa0ed126a337c6fae6624704`; the manuscript is not copied here.

Incoming CI results validate their own source heads. This integration needs
its own complete build and transitive audit. The local machine-readable receipt
is `notes/verification/negative_classification_2026-11-13.json`.

## Mathematical review of the closing proof

1. `OddToggleP3ActualShiftedBadTrialContradiction` takes an actual shifted bad
   raw source word to a forbidden genuine parent packet. It uses the increasing
   enumeration of the real transversal and two fresh vertices, identifies all
   raw mixed facets with actual canonical orientations, and identifies the
   endpoint with the preserved right side. Switching parity forces the last
   sign. No synthetic parent orientation is substituted.
2. `OddToggleP3AllShiftedBadNoCanonicalJoint` obtains one F2 cochain valid
   simultaneously on all selected mixed facets of an arbitrary genuine joint.
   Its degree-4k coefficients give one supported Boolean gauge. The bad trial
   for that gauge contradicts item 1. The theorem ranges over every genuine
   canonical joint, without choosing a preferred completion.
3. `OddToggleP3RealOddLinkSideDisagreement` turns odd link-source parity into
   different canonical signs on the same set of exactly `4*k+3` vertices.
   The sign-to-orientation bridge gives an actual injective tuple of the
   original structures. It excludes identification of their fresh vertices.
4. `OddToggleP3BadOnePointSourceTemplate` uses full side-age results for
   arbitrary source coefficients and proves agreement over the common base.
   Items 2 and 3 rule out the distinct and identified cases of an ordinary
   amalgam. The resulting object meets the original `HasBadOnePoint` definition.
5. `OddToggleP3AllBadOnePoint` chooses the explicit positive block size
   `t = 2^(m+1)*m^(m-2)` with `m = 4*k+2`. The all-zero trial exists in
   `ZMod t`; `NeZero t` is proved from positivity. The finite all-gauge theorem
   gives one source assignment meeting both events. Its shift is the actual
   coboundary gauge, and its bad-W choice is the genuine endpoint functional.
   This discharges `OddP3OnePointObstructions` for every `k >= 1`.

Reviewed critical interfaces include `Hyper`, `Preserves`, `localIndex`,
`ValidTypes`, `switchingAllowed`, `HasAP`, `HasBadOnePoint`, the ordinary
one-point/canonical-union bridge, the full side-age statements, the universal
actual mixed-gauge statement, and the all-gauge finite counting theorem.
The existing induction gives exactly `NecessaryAlternatives`, assuming only
arity at least four, valid allowed indices, central membership, and ordinary AP.
There is no remaining exceptional-family premise, order-preserving embedding
restriction, strong-AP hypothesis, or finite-Ramsey premise.

This is a focused review of the final source proof and its critical interfaces,
not a claim of independent line-by-line re-review of every historical module.
The kernel build and transitive audit cover the entire imported project.

## Integration and tooling

The merge preserves source history. The two conflicts are only in the facade
and readable audit registry. Their resolution retains every old import and
axiom print and appends the final exports. `NegativeClassification` supplies
the public theorem name and ordinary non-AP contrapositive with unchanged hypotheses.

Two historical `import Mathlib` foundation imports made small consumers take
around 50 seconds locally. Specific imports replace them; tactics and missing
mathematical definitions are imported in their actual consumers. A few unit-sign
simplifications are explicit instead of relying on the full global simp set.
The theorem statements and construction choices are unchanged. The full consumer
build is required after this cleanup; old green CI does not validate changed imports.

The old readable audit did not enforce the full axiom allowlist. In particular,
the two arity-five Boolean seeds used `bv_decide`, whose native certificate
check extends the trusted base. These are replaced by Mathlib's `lrat_proof`
propositional proof reconstruction. The arity-four raw fifteen-bit certificate
also uses this path to avoid a memory-heavy exhaustive function enumeration.
There are 211, 70 and 47 CNF clauses respectively. Small three/four-Boolean
lemmas certify the translation from the original rules to each forbidden clause;
the original semantic packet bridges and hypotheses remain unchanged. Every
LRAT inference becomes a kernel-checked logical proof, without native evaluation
axioms. `tools/generate_finite_certificates.py` can regenerate the inline CNF/LRAT
data with CaDiCaL; neither this script nor the SAT solver is trusted.

The Lake manifest is versioned rather than restored from a cache. CI uses its
identity in dependency-cache keys, checks the proposed commit itself, derives
cache roots from actual imports, checks complete facade coverage, and enforces
the full defining-module transitive axiom allowlist. The audit tool is pinned
to `46024e005996495c65ef609368e11ab39c4222e3` (v0.1.2) and built with the receiving compiler.

## Result boundary

This milestone is the necessary condition and the corresponding ordinary
non-amalgamation result for arities at least four. Positive SAP constructions,
unboundedness equivalence, main-paper Ramsey/EPPA results, and small-arity side
claims are subsequent work. Five-constrained ternary classification is postponed.
