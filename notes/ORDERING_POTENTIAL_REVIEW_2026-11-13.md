# Independent ordering and potential review, 2026-11-13

Source: `shulda/tex_hypertournaments` at
`919349e7eceed3c7fa0ed126a337c6fae6624704`, especially
`thm:ordering`, the potential existence/switching lemma, and `thm:potential`.
This note records a mathematical and API review of the new working-tree
modules, separately from their kernel and axiom checks.

## Ordering property

Reviewed `OrderedJointEmbedding`, `AllOrderHost`, `OrderedPair`,
`PairOrderHomogeneity`, and `PairOrdering`. No blocking issue found.

- `pair_cancelling_ordering_property` chooses the finite carrier and its
  underlying hypertournament before quantifying over both the source and
  target orders. Thus the witness has the quantifier order required by the
  article, rather than depending on either order.
- `orderExpansionReindex` sends a newly ordered source into a permutation
  pullback with one fixed order. The pullback is on the intrinsic orientation;
  its verification uses the permutation and its inverse, so no unproved
  order-invariance of an orientation is assumed.
- The finite host really is constructed by repeated proved SAP/JEP. It
  contains all permutation-indexed order expansions and a separately supplied
  ordered pair. This anchor supplies the baseline pair even when the original
  source is empty or has one vertex.
- Since the hypertournament arity is at least three, every injection of the
  two-point model preserves its orientation. Consequently all increasing
  pairs in the homogeneous copy are tested by the coloring. A false color
  gives strict antitonicity using injectivity; a true color gives strict
  monotonicity.
- In the antitone case the source order is replaced by its dual. The
  all-orders host already contains that expansion, and composing two order
  reversals is increasing in the originally requested source and target
  orders. The intrinsic source hypertournament remains the same.
- Pair omission follows from the actual size lower bound in `PairCancelling`;
  no unmentioned assumption about the forbidden family is needed.

The exported final ordering theorem uses finite carriers in `Type`; the
supporting host and pair-homogeneity lemmas are universe-polymorphic. Its
statement does not assume a nonempty source.

## Binary ordering base case

Reviewed `BinaryPair`, `BinaryPairHomogeneity`, `BinaryOrderHost`, and
`BinaryOrdering`. No blocking issue found. The proof does not identify the
two genuinely distinct ordered two-vertex tournament types.

The first Ramsey stage homogenizes the false increasing-edge type into a
host containing every ordered expansion of the source and an ordered directed
triangle. The second stage homogenizes the true increasing-edge type into a
host for that first witness. After the target order is chosen, the first
homogeneous copy is selected inside the second, using the coloring composed
with its embedding. Thus the composite is homogeneous separately for both
types; the homogeneity obtained at the outer stage is retained upon
restriction.

The ordered triangle has increasing-edge bits false, false, true. Its two
successive edges therefore have the same comparison color. If the long edge
had the other color, the new linear order would violate transitivity, in
either possible direction. The proof explicitly checks both contradictions.
Both edge types consequently have a common comparison color on the whole
copy, which makes its vertex map globally increasing or globally decreasing.
The same all-orders/dual-order argument then finishes the ordering property.

The triangle anchor also handles empty and singleton original sources. As in
the higher-arity theorem, the final underlying witness is chosen before both
orders. `unrestricted_ordering_property` splits off exactly arity two and uses
the already reviewed empty-forbidden-family theorem for higher arities.

## Intrinsic potential interface

`EvenPotential` proves the actual equation on every injective ordered tuple,
not just a normalized or canonical sign equation. The cone contraction first
produces a scalar cochain on canonical subsets, and equality of the two
alternating upper orientations then recovers all tuple orientations.

`Hyper.exists_potential` and `Hyper.isEven_iff_exists_potential` quantify over
arbitrary finite carriers, including the empty carrier. They need `Even r`
for the lower arity and do not need a positive lower bound on `r`.
`isPotential_iff_coboundary_eq` identifies the raw equation with the actual
intrinsic equality `φ.coboundary hr = A`.

`IsPotential.preserves` is in the useful direction for expansion arguments:
preserving the chosen lower potential implies preserving the upper
orientation. Restriction and equivalence transport use arbitrary vertex
injections/equivalences, without adding order-preservation hypotheses.

The zero-arity empty-carrier case requires care only for later gauge results.
On the empty carrier there are two zero-arity orientations and a unique
one-arity orientation; both lower orientations are vacuous potentials of it.
A scalar coboundary vanishes on the empty subset, so those two potentials
are not gauge equivalent. The canonical gauge theorem has an explicit anchor,
and relative extension in the article is used with `r ≥ 2`; neither makes
that invalid claim.

## Relational expansion language

Reviewed `PotentialLanguage`. No blocking issue found. The language really
names both the lower relation of arity `r` and upper relation of arity `r+1`,
in addition to the free linear order. `liftPotentialEmbedding` supplies full
`map_rel_iff`, including reflection, for all three symbols. Its upper
relation field uses the proved equivalence between intrinsic preservation and
relation equivalence on arbitrary tuples; repeated coordinates are therefore
included correctly. `forgetPotentialEmbedding` preserves the same vertex map
and retains both the lower relation and order.

## Ramsey transport

Reviewed the complete `PotentialRamsey` proof. No blocking issue found.
`potentialExpansionClass` includes finiteness of the whole carrier and the
actual potential equation, not an unspecified class provider. Its members are
precisely the freely ordered, named potential expansions in the intended
language; the potential equation already entails evenness of their upper
orientation.

For an arbitrary coloring of full expansion embeddings, the proof colors a
lower-potential embedding by lifting its actual vertex map. The unrestricted
ordered Ramsey theorem then supplies a lower-potential witness and a
homogeneous lower embedding of the target. Its intrinsic coboundary supplies
the upper witness. For every two full embeddings into that target, forgetting
their upper relation produces the two lower embeddings to which homogeneity
applies. The displayed equality proved with `Embedding.ext` identifies each
lifted composite with the composite in the full expanded language. Hence the
final coloring equality concerns all genuine full expansion embeddings, with
the required preservation and reflection of both orientations and the order.

Both the explicit witness theorem and the native class Ramsey theorem require
`Even r` and `2 ≤ r`. They cover the binary-potential/ternary-upper case using
the proved unrestricted arity-two Ramsey input. The finite nonempty color
palette is universally quantified. The witness also explicitly proves
evenness of its upper orientation.

The expansion-property argument of `thm:potential` is a further obligation;
this Ramsey transport theorem, the plain ordering property, and existence of
potentials do not by themselves prove that assertion.

## Verification

`lake build Hypertournaments.EvenPotential` passed (1631 jobs). Focused
`#print axioms` checks for existence, the existence/evenness equivalence,
canonical gauge, preservation, and the intrinsic-coboundary equivalence all
reported exactly the allowed axioms `propext`, `Classical.choice`, and
`Quot.sound`. No forbidden proof placeholders or native proof shortcuts occur
in `EvenPotential.lean`.

An independent build of `PairOrdering`, `PotentialLanguage`, and
`PotentialRamsey` passed (1777 jobs). Focused axiom checks of
`pair_cancelling_ordering_property`, `exists_potential_ramsey_witness`, and
`potential_expansions_ramsey` also reported exactly the same three standard
axioms. The binary review inspected the completed sources without requesting
another full source rebuild; focused axiom checks of
`binary_ordering_property` and `unrestricted_ordering_property` reported the
same standard allowlist.
