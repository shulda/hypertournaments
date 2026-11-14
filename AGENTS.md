# Hypertournaments formalization

The user has transferred ownership from the former Chat project to this Work
project. Preserve its source branches and commit history. No multi-project
claim queue is needed. The current scope is the main hypertournament article
and the negative (n+1)-constrained classification for n >= 4. The separate
five-constrained ternary census is postponed.

Scope update, 2026-11-14: the user excluded `cor:sullivan-ramsey` and its
infinite antichain/Fraisse infrastructure from the formalization. The final
`Further potential constructions` section is now included: arbitrary finite
involutive palettes and finite abelian effective groups, with actual SAP,
Ramsey, precompactness and expansion properties. Duplicate fiber codes must
retain one fixed target code across every later potential and vertex order.

Keep `Hyper`, `Preserves`, `HasAP`, the local-index palette, and the cochain
API shared. Read the actual theorem signatures and mathematical source before
using a result. A conditional reduction is unfinished until every source
instance has been proved. Keep ordinary AP distinct from strong AP, and
orientation-preserving embeddings distinct from order-preserving embeddings.

Use Lean 4.34.1 and the committed Lake manifest. Do not introduce `sorry`,
`admit`, custom axioms, or stronger hypotheses to fill a proof gap. Production
files import specific Mathlib modules and tactics in the files that use them;
do not restore `import Mathlib` or `import Mathlib.Tactic` in a shared foundation.

Check `python3 tools/project_sources.py`, `lake --rehash build`, the readable
`Hypertournaments/AxiomAudit.lean`, and the complete defining-module axiom audit
with allowlist `propext,Classical.choice,Quot.sound`. Every public source module
belongs in the `Hypertournaments.lean` import closure. CI must validate the
actual proposed commit; an older green head does not validate new imports.

The main article source is in the private `shulda/tex_hypertournaments` repo.
Record the exact source commit for each work package. The original negative
argument is `notes/negative_general_arity_audit_v4.tex`. Preserve source-linked
review notes and explicit remaining obligations. Do not copy the private
manuscript wholesale into this public repository.
