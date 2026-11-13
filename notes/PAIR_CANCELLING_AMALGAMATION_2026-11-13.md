# Pair-cancelling completion and strong amalgamation

## Sources

- Main article: private `shulda/tex_hypertournaments`,
  `919349e7eceed3c7fa0ed126a337c6fae6624704`, pair-cancelling definition,
  `prop:link-completion`, and `prop:link-SAP`.
- The current article head inspected during this work was
  `046562a498165260e6910a235d23dc5820190fd2`. Its only source differences
  from that pin are two cosmetic sentences in the abstract/introduction;
  the mathematical source for this package is unchanged.
- The direct highest-ranked-missing-pair proof is section 3 of the prepared
  formalization source. It replaces the article's iterative schedule.
- The pure finite order shuffle is adapted from
  `CCO/UnaryHN/Ordered/Shuffle.lean`, `shulda/lean_cco` at
  `48a6f3d8bf02bb0dfeb30f69bec8e9d0afa764e6`. Its small Mathlib import
  closure is used; this project does not depend on the CCO package.

## Definitions and actual theorem scope

`Hyper`, `Preserves`, and `Hyper.pullback` are unchanged. `PartialHyper`
records an optional Boolean on each injective tuple, with the corresponding
alternation law. Its `none` entries are genuinely unspecified.
`HasCliqueDomain` specifies its domain by missing pairs and tuple ranges;
that proposition is independent of a chosen decidable equality or order.

`PairCancelling` includes arity at least three and at least n+1 vertices.
For every distinct ordered pair and every auxiliary linear order, it supplies
two different orientations on tuples beginning with that pair and having
increasing tails. Only the tail is ordered. Quantifying over orders of the
whole finite carrier is equivalent to the paper's complement-order convention,
since every order on the complement extends to the whole carrier.

`ForbiddenFamily n` is an arbitrary, possibly infinite family of finite
structures, indexed by finite cardinalities. `Omits` forbids actual
orientation-preserving embeddings; there is no order restriction on them.

`exists_pair_cancelling_completion` takes a consistent partial orientation
with the clique domain and no fully prescribed forbidden copy. It produces
an actual forbidden-free `Hyper` on the same carrier, retaining every specified
orientation. A finite injective rank is constructed internally. There is no
rank provider, completion provider, Ramsey hypothesis, or missing instance.

`pair_cancelling_strong_span` applies this to arbitrary compatible finite
spans. Its literal carrier is `B ⊕ (C \ range g)`. The carrier lemmas prove
commutation, union coverage, and exact overlap. The theorem keeps those same
injections and proves both orientation preservation statements.
`pair_cancelling_hasStrongAmalgamation` transports the result to the finite
`Fin` presentation, including its explicit exact-overlap clause.
`pair_cancelling_ordered_strong_span` additionally supplies a common linear
order preserving both prescribed side orders. Thus both ordinary omission
classes and their free ordered expansions have strong amalgamation.
Empty bases and empty sides are included in the quantified interfaces.

`preserves_iff_relation` proves the induced relational encoding on all tuples:
R means injectivity and orientation `false`. It includes reflection and the
exclusion of repeated-coordinate tuples.

## Proof review

The constant-link template embeds the two distinguished vertices as the two
new bottom elements of `WithBot (WithBot V)`, retaining the old order on the
tail. Constant canonical signs there give exactly zero on the requested link.

Each unprescribed n-set uses the template of its highest-ranked missing pair.
For a hypothetical forbidden image Y, the last pair of Y stays last in every
n-subset of Y containing it. All its increasing link tuples therefore have
orientation zero. Pulling the target order back along the hypothetical
embedding gives a contradiction with the actual forbidden structure's
pair-cancellation witnesses. If Y has no missing pair, its whole orientation
was prescribed and contradicts partial omission instead.

In the free partial union, a fully prescribed forbidden copy lies on one side.
Otherwise a cross pair is contained in one of its pair-link witness tuples,
which cannot be prescribed by the clique-domain equation. Compatibility over
the exact common base makes the partial union preserve both sides.

The finite order shuffle uses cut/base/side/rank labels and an injective final
tie breaker. It extends both original orders, including the empty-base case.
A separate supporting review checked the PC quantifiers, template, stabilization,
arbitrary embeddings, relational convention, and exact-overlap transport.

## Validation and remaining work

The machine-readable build and complete axiom-audit receipt is
`notes/verification/pair_cancelling_amalgamation_2026-11-13.json`.
All new source modules belong to the audited project facade.

The orientation-component completion theorem is not yet the full
arbitrary-relational `prop:link-completion`. The Ramsey transfer still needs
the adapter from arbitrary R,< structures satisfying the irreducible-piece
hypothesis, together with the identity homomorphism-embedding conclusion.
`RelationalEncoding` is not yet a StructuralRamsey language instance.

The local-type equivalence `PC iff d <= q-2` remains a separate lemma, needed
to instantiate the first positive direction of the constrained classification.
Potential/switching SAP supplies its other positive direction. No claim that
the full positive classification or the Ramsey theorem is finished is made by
this package. Five-constrained ternary classification remains postponed.
