# General affine potential constructions

Article source: `shulda/tex_hypertournaments` at
`919349e7eceed3c7fa0ed126a337c6fae6624704`, final subsection
`Further potential constructions`.
Parent main: `3ab7e8a3ac2d936086b9d29d369801cadfaba833` (PR #415).

The user included this subsection in the formalization on 2026-11-14 and
excluded `cor:sullivan-ramsey` and its infinite antichain/Fraisse dependencies.
The separate five-constrained ternary classification remains postponed.
The existing `Hyper`, `Preserves`, local-index, and even-potential APIs
are retained. This package adds a general layer in `Hypertournaments.Affine`.

## Parameters and original mathematical conclusions

`Palette Q` consists of an involution on the raw labels, allowing fixed
labels. `Data Q G` additionally specifies an abelian group, offset `a`,
and a surjection `effective : Q -> G` with
`effective (star q) = a - effective q`.

With lower potential arity `r` and upper raw arity `n = r+1`, the source
condition is exactly `Even (r+1) -> a = 0`. The article assumes `n >= 3`.
The potential involution is `g -> a-g`. `Labelled` records values on actual
injective tuples with the required transposition law. Its preserving maps
are the original arbitrary vertex injections preserving all labels.

| Source assertion | Actual exported Lean result |
| --- | --- |
| Signed coboundary squares to zero | `signedCoboundary_signedCoboundary_zero` |
| Correct affine permutation law | `Labelled.coboundary` and `signedCoboundary_label_perm` |
| Closed effective labels iff potential exists | `closed_iff_exists_potential` |
| Equal potentials differ by a signed lower gauge | `exists_signed_gauge`, `IsPotential.exists_gauge` |
| Align a prescribed base potential | `IsPotential.exists_aligned` |
| Strong amalgamation of expansions | `expanded_strong_span` |
| Strong amalgamation of closed reducts | `closed_strong_span` |
| Actual expanded Ramsey witnesses | `exists_expansion_ordered_ramsey_witness` |
| Full native Ramsey class | `expansion_ordered_ramsey` |
| Expansion property relative to closed reducts | `expansion_property` |
| Finite relational language | `expansion_language_rel_finite`, `expansion_language_func_empty` |
| Finitely many expansions on each finite reduct | `ordered_expansions_finite` |

Finite raw and effective palettes give all the source conclusions together.
The algebra is proved for arbitrary abelian groups. Several amalgamation
and Ramsey statements also hold without palette finiteness; the finite
effective group is used as the gauge-color palette for expansion property.

## Signed algebra and affine exactness

`SignedCoboundary` uses the literal sum
`sum i, (-1 : Int)^i.val • value (facet tuple i)`. The two deletion orders
have equal remaining tuples and opposite integral coefficients, giving
`Delta squared = 0` by a fixed-point-free involution. All calculations are
in an arbitrary additive commutative group.

The adjacent-transposition calculation has affine defect equal to `a` in
odd upper arity and zero in even upper arity. This proves the actual
permutation law under the displayed source condition. It does not replace
the affine involution by ordinary negation when `a` is nonzero.

`SignedContraction` and `SignedExactness` prove ordinary alternating
exactness by an explicit root cone, including the root-containing case,
all positive degrees, and empty carriers. `Potential` then chooses one
affine base cochain using an auxiliary order. Subtracting its coboundary
from the closed effective cochain gives an ordinary alternating cocycle.
Ordinary exactness and addition of the base cochain yield the required
affine potential. The finite-carrier theorem hides the auxiliary order.
No division by two or characteristic-two hypothesis occurs.

Differences of potentials are ordinary alternating cochains. Their signed
lower gauges extend by zero outside an arbitrary embedded base. Shifting
the side potential by the extended coboundary retains all raw effective
labels and aligns the actual base tuple functions.

## Actual strong amalgams

The generic `labelled_strong_span` completes compatible side labels on
the original `FiniteStrongSpan.Carrier`. For potential expansions, an
order on that carrier induces compatible side and base presentations.
Their independent potential labels and oriented fiber codes amalgamate;
decoding returns the actual original raw labels on both sides. The
temporary orders do not enter the theorem's hypotheses.

For closed reducts, the side potentials exist by the proved equivalence.
A signed lower gauge aligns their base restrictions before expanded
amalgamation. Both conclusions retain exactly the original carrier
injections, so the existing commutation, exact overlap, and coverage
theorems apply. Empty bases and empty sides are included.

## Fiber codes and native Ramsey witnesses

The independent upper palette is `Q × Bool`. The first coordinate is an
auxiliary color and the second is its orientation. Uniformly using `Q`
as the color bound avoids any assumption about equal fiber sizes.

For each effective value, an already-correct raw label is retained;
otherwise surjectivity chooses a member of that fiber. The true sheet
uses the opposite fiber and the original raw involution. This proves
equivariant decoding, including fixed raw labels and duplicate codes.
Every raw label has a false-sheet code in its correct fiber.

`PairLanguage` names arbitrary independent labels in the two arities.
`PairRamsey` obtains actual finite ordered witnesses directly from the
existing pinned ambient relational Ramsey theorem. Its canonical decoder
handles missing or multiple candidate labels outside encoded copies and
preserves every fully encoded source/middle copy on the original vertex
map. All named label relations and the order are reflected, including
repeated-coordinate tuples.

`ExpansionRamsey` canonically encodes the two source expansions and then
decodes the pair witness. Actual embedding maps compose pointwise, so
the transported coloring yields precisely native `Structure.Arrow` in
the original language naming raw labels, a potential, and the free order.
The full class theorem includes the constructed witness's actual finite
carrier and membership. No uninstantiated provider remains.

The underlying 119-module Ramsey closure and its compiler options are
unchanged at source `48a6f3d8bf02bb0dfeb30f69bec8e9d0afa764e6`, digest
`ae194b3154e25d52e71523b0b8eae966acb6f5c851dc94e2aed9c52ef1ab3422`.

## Expansion property with duplicate codes

The fixed witness is obtained as one intrinsic independent pair
`(basePotential, fixedCode)` before any later target potential or order.
Its raw reduct is obtained by equivariant decoding. Every later potential
has the same effective coboundary, so `decode_fixed_code` reconstructs
the same raw reduct using that same code. The proof never needs to recover
a unique code from a raw label or recode the witness in its new order.

`PairOrderHost` supplies an actual finite host containing every independent
pair on the source carrier with every order and a small anchor.
`PairOrdering` proves the full ordering property, including binary lower
arity and fixed-point palettes: for each old pair, a new point supplies
two edges of one fixed ordered type. Homogeneity of that type and order
transitivity force a common direction on every old pair. This yields the
required monotone or antitone copy after choosing a source order.

The Ramsey step homogenizes the actual signed lower gauge, with colors in
the finite effective group. Its drift on increasing potential tuples is
zero in even potential arity and the common color in odd potential arity.
The all-model host supplies the source pair shifted by the negative drift.
The shifts cancel on canonical tuples; intrinsic reconstruction gives
preservation on every tuple. The code is retained throughout. The result
is an actual embedding preserving raw labels, potential labels, and orders,
for every source/target potential and order over one fixed finite target.

`Precompactness` proves finiteness on the fixed carrier itself, by coding
orders as Boolean comparison tables and using finite potential tables.
The range of actual native expanded structures is finite. Function symbols
are absent and the label-and-order relation-symbol set is finite.

## Recovery of the original even construction

`EvenSpecialization` uses the Boolean raw involution, effective group
`ZMod 2`, and offset one. It supplies actual two-way equivalences between
the old `Hyper`, Boolean-labelled structures, and affine group-labelled
structures. The signed and unsigned tuple operators agree on every tuple.
Closedness, potential equations, preserving injections, and actual
coboundaries agree in both directions. The original finite potential
existence theorem is recovered from the new general result without using
its previous existence proof.

## Reviews and verification

Independent reports cover every new module:

- `AFFINE_SIGNED_ALGEBRA_REVIEW_2026-11-14.md`
- `AFFINE_SIGNED_COBOUNDARY_REVIEW_2026-11-14.md`
- `AFFINE_POTENTIAL_REVIEW_2026-11-14.md`
- `AFFINE_PAIRS_REVIEW_2026-11-14.md`
- `AFFINE_AMALGAMATION_REVIEW_2026-11-14.md`
- `AFFINE_CODE_AND_EXPANSION_REVIEW_2026-11-14.md`
- `AFFINE_SPECIALIZATION_REVIEW_2026-11-14.md`

The receipt `verification/affine_potentials_2026-11-14.json` records the
complete rehashed build, source/facade and immutable vendor checks, ten
source-guard regression tests, readable endpoint checks, all four complete
defining-module axiom audits, and source/configuration hashes. The allowlist
is exactly `propext,Classical.choice,Quot.sound`. Review examples include
nonzero offsets over `Int` and `ZMod 3`, noninjective effective maps,
fixed raw labels, duplicate oriented codes, both arity parities, empty
carriers/bases, and higher carrier, palette, and color universes.
