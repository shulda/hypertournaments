# Ordering, intrinsic potentials and switching amalgamation

## Source and scope

Mathematical source: `shulda/tex_hypertournaments` at
`919349e7eceed3c7fa0ed126a337c6fae6624704`, `thm:ordering`,
`lem:alternating-sums`, `prop:potential-SAP`, and both assertions
of `thm:potential`. The expanded proof preparation adds the binary potential
base case and spells out the empty-carrier cases. No private manuscript
source is copied into this repository.

This package extends main `861b92cc2371ca947fff4fab3c88559723a72622`.
It retains the shared `Hyper`, `Preserves`, local-index palette and ordinary
`HasAP` interfaces. No compiler, Mathlib, provider-source, or manifest pin changes.

## Ordering and the binary base

`Ramsey.pair_cancelling_ordering_property` constructs one finite
forbidden-free target before quantifying over the two free vertex orders.
Finite ordered JEP supplies a host containing every order expansion of the
source and an ordered pair. The pair comparison coloring and the proved
Ramsey theorem yield a monotone or antitone copy. In the latter case, the
host contains the source's dual order. Intrinsic orientations never change
when these auxiliary orders are replaced.

The pair object is unique only for arity at least three. `BinaryOrdering`
therefore proves tournaments separately: two Ramsey stages homogenize their
two actual ordered edge types. A directed triangle makes the two comparison
colors equal. The same monotone/antitone argument then proves binary ordering.
The combined unrestricted theorem covers every arity at least two.

`UnrestrictedAmalgamation` and `UnrestrictedRamsey` discharge the binary
completion, ordered SAP, local-finiteness and Ramsey hypotheses directly.
The existing empty-family completion works for arity two; no binary
pair-cancelling definition or unproved Ramsey provider is introduced.

## Intrinsic coboundaries and potentials

`tupleCoboundary` sums raw orientation bits over deleted coordinates of an
actual injective tuple. Its square is zero by a fixed-point-free involution
on the two deleted coordinates. This short intrinsic proof is shared by
all subsequent tuple arguments; the existing subset-cochain contraction
and double-coboundary proofs are reused for existence and gauges.

For even r, `Hyper.coboundary` produces an actual `(r+1)`-hypertournament,
with its swap law proved from adjacent transpositions. It is even and
commutes with every vertex embedding, not merely increasing embeddings.

`IsPotential A φ` is the equation on **every** injective ordered tuple.
`Hyper.exists_potential` proves it on arbitrary finite carriers. The scalar
cone contraction first constructs canonical signs, and alternation recovers
the complete tuple equation. The empty carrier is handled before selecting
an anchor. Existence also holds at r=0; that does not imply gauge exactness
on the empty carrier in degree zero.

`EvenPotentialGauge` proves intrinsic exact gauge equivalence in positive
degree, extension of gauges by zero along arbitrary injections, and relative
potential alignment. In particular, a chosen potential on a finite base
extends over a larger even structure without changing its upper orientation.
Positive degree is explicit; the article uses r at least two.

## Actual amalgams and the switching palette

`potential_strong_span` and its ordered variant glue compatible lower
potentials on `FiniteStrongSpan.Carrier`, then take the intrinsic coboundary.
This carrier identifies exactly the original base. The unexpanded
`even_strong_span` first aligns the two potentials on that base. Its ordered
variant extends both given orders. Empty bases and arbitrary source
embeddings are covered.

`Hyper.admissible_switching_iff_isEven` identifies the raw evenness condition
with the **existing** switching palette in every odd arity, including both
congruence classes modulo four. `switching_hasAP` then supplies ordinary AP
for that palette for every odd arity at least three. The stronger span
theorem retains the exact-overlap carrier.

## Ramsey for the full expanded language

`PotentialLanguage` names three relations: the lower potential, the upper
orientation and the free linear order. Lifting an ordered potential embedding
proves preservation and reflection of the upper relation from the intrinsic
potential equation. Forgetting it retains the same vertex map.

`exists_potential_ramsey_witness` transports the fully proved unrestricted
Ramsey theorem through these two maps. Lifted composites are checked equal
to the composites of full expanded embeddings. The exported
`potential_expansions_ramsey` is the actual native Ramsey class, with
whole-carrier finiteness and no unproved provider premise. The binary lower
arity, hence ternary upper arity, is included.

## Full expansion property

`potential_expansion_property` chooses a finite even upper witness before
both source/target potentials and both free orders. A finite host contains
all lower orientations of the source carrier, which also covers all its
ordered potentials by permutation pullback. Apply Ramsey for the unique
ordered model on r-1 vertices, then the unrestricted ordering property to
choose a lower witness before the eventual target order.

Any target potential differs from that chosen lower witness by an exact
symmetric gauge. Each facet is proved to be the actual image of a small-model
embedding. Ramsey homogeneity makes all its gauge contributions equal; their
r-fold sum vanishes because r is even. The constant color is arbitrary and
need not be zero. The resulting **same** vertex embedding preserves the new
potential, and lifting it preserves both named orientations and the order.
The argument also covers empty/small sources: whenever an r-tuple is tested,
one of its facets supplies a local color baseline.

## Verification and remaining work

Independent mathematical/API reviews are recorded separately in
`ORDERING_POTENTIAL_REVIEW_2026-11-13.md` and
`EVEN_AMALGAMATION_REVIEW_2026-11-13.md`, with the full expansion argument
reviewed in `POTENTIAL_EXPANSION_REVIEW_2026-11-13.md`. The full source/build/axiom receipt
is `verification/ordering_potentials_2026-11-13.json`. The four defining-module
prefixes are audited with exactly `propext,Classical.choice,Quot.sound`.
The facade includes every new public proof module.

The finite-group/EPPA arguments and their consequences, the
local-type pair-cancellation cutoff and the remaining positive classification
links are separate article tasks. Five-constrained ternary classification
remains postponed.

## Next group-theoretic unit

A read-only check of the pinned Mathlib favors the elementary Sylow/Klein
route over importing a new coprime-centralizer generation theorem. Relevant
existing inputs include `MonoidHom.FixedPointFree.coe_eq_inv_of_involutive`,
`Sylow.pointwiseMulAction`, `Sylow.card_dvd_index`,
`IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card`,
`Group.normalizerCondition_of_isNilpotent`, and `Sylow.mapSurjective`.
The remaining work is to construct compatible restricted and quotient actions;
the general centralizer-saturation assertion is not yet proved here.

An economical first hypertournament unit is odd order of the pointwise
stabilizer of n-2 vertices. It should use a minimal intrinsic automorphism
group, Cauchy's theorem (`exists_prime_orderOf_dvd_card'`), and the existing
two-point tuple/swap argument. The isolated Klein fixed-point prototype in
the proof preparation can be ported alongside that work. These are next-step
recommendations, not additional formalized conclusions of this package.
