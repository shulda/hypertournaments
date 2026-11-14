# Independent affine potential review, 2026-11-14

Source: `shulda/tex_hypertournaments` at
`919349e7eceed3c7fa0ed126a337c6fae6624704`, final subsection
`Further potential constructions`. Reviewed frozen
`Affine/LinearOperations.lean`, `Affine/PotentialBasics.lean`,
`Affine/Potential.lean`, and `Affine/Precompactness.lean` against the
actual labelled tuple structures, signed coboundary, effective-label
data, and native expansion language.

No blocking mathematical or API issue was found. The reviewer did not
modify the four reviewed proof files. The ordinary signed exactness
used here has its separate construction and review; this note checks
the affine reduction and raw-label interfaces.

## Affine operations and actual potential equations

Subtraction of two tuple structures with common involution `x ↦ a - x`
has the ordinary involution `x ↦ -x`, since the affine offsets cancel.
`Labelled.affineSub` proves this on every actual swapped injective tuple.
Conversely, adding an ordinary alternating term to an affine-labelled
structure retains the original affine involution. The zero object is
correctly supplied only for the ordinary offset-zero palette.

`IsPotential` retains the actual raw palette structure and equates its
effective labels with the signed coboundary on every tuple. Pullback
uses the original arbitrary vertex injection and the literal induced
structures. The proof of closedness replaces each effective facet value
by the given potential equation and then applies the actual integral
`Delta^2 = 0` theorem.

The difference of two potentials for the same raw structure is therefore
an actual closed ordinary alternating cochain. There is no replacement
by a symmetric function on unordered supports, and no characteristic-two
assumption.

## Exactness after subtracting an affine base

The ordered existence theorem chooses an actual affine-labelled base
cochain from the constant-zero canonical table. This does not assert
that all raw tuple values of that base are zero: odd reorderings apply
the affine involution and may produce the offset.

Its actual signed coboundary is an affine-labelled upper structure by
the proved permutation theorem. The hypothesis
`Even (r + 1) -> a = 0` is exactly what allows that upper structure to
retain the prescribed affine offset. Subtracting it from the given
closed affine upper cochain produces a closed ordinary alternating
cochain. Ordinary exactness supplies a lower ordinary term. Adding that
term back to the affine base recovers the original upper cochain on
all injective tuples.

This proof requires neither division by two nor any restriction on the
torsion of the coefficient group. The ordered theorem needs only an
auxiliary linear order on the carrier. The finite-carrier wrapper chooses
such an order through `equivFin`; its conclusion and preservation notions
do not retain the chosen order. Empty carriers require no extra premise.
Neither theorem assumes a finite coefficient group or a finite palette.

## Raw fibers and signed gauges

`closed_iff_exists_potential` applies the construction to the effective
labelled structure of the original raw object. It does not replace the
raw labels by their images, change their fibers, or assume that the
effective map is injective. Its hypotheses are the actual `Data` record,
the parity condition, and a finite carrier. Source finiteness of group
and palette is not used by this algebraic implication.

The preservation theorem deliberately concludes preservation of
`d.effectiveLabelled raw`, not preservation or uniqueness of raw labels.
This is the correct boundary when the effective map has nontrivial
fibers. No reviewed result claims that a potential determines a unique
raw structure.

`IsPotential.exists_gauge` is indexed with potentials in arity `r + 1`.
It returns a genuinely alternating gauge in arity `r`, with the literal
signed coboundary equation. Thus the statement covers every positive
potential degree without a natural-subtraction cast or an invalid
degree-zero exactness assertion. No finiteness assumption is needed
for this difference statement.

## Literal finite-language precompactness

The ordered expansion language has relation symbols exactly
`(G + Q) + Unit`: one symbol for every actual potential label, every
actual raw label, and the free order. The finite-language theorem
correctly assumes both `Finite G` and `Finite Q`. Its function-symbol
type is literally empty, with no finiteness assumption needed to prove
that fact. These statements match the imported `PairLanguage` and
`ExpansionLanguage` definitions.

On a fixed finite carrier, a linear order is injected into its Boolean
table of comparisons. Equality of those tables gives equality of the
order by `LinearOrder.ext`; it does not identify distinct actual orders
merely up to isomorphism.

`FixedExpansion` consists of an actual compatible potential and an actual
free linear order over one fixed raw structure. Its finiteness uses
only the finite coefficient group and finite carrier. The raw palette
need not be finite for this fixed-reduct statement, since no new raw
labels are chosen. Finally `fixedExpansionNative` constructs the actual
native ordered expansion, and finiteness of its range follows from
finiteness of this typed domain. Thus the result holds before taking
isomorphism classes. Existence of expansions for closed reducts comes
from the potential theorem; the finite-range theorem does not silently
assert existence for arbitrary unclosed reducts.

## Validation and frozen snapshots

An independent three-target build passed (1122 jobs). The only replayed
warning was the pre-existing unused-`change` warning in
`FinitePresentation.lean`; the three reviewed modules produced no warning.
Ten focused axiom prints covering the operations, closedness,
effective preservation, both existence theorems, the main equivalence,
and gauge wrapper reported exactly `propext`, `Classical.choice`, and
`Quot.sound`.

An independent precompactness target build also passed (1111 jobs).
Six further axiom prints, including both language claims, stayed within
the same allowlist; the empty-function claim uses only `propext`.

Six additional kernel-checked examples cover offset seven over the
infinite group `Int`, existence on an infinite ordered carrier, empty
carrier existence, the degree-one potential/gauge boundary, and a
two-element effective fiber. In the fiber example two distinct actual
raw structures have the same effective labels and the same potential;
the formal interfaces correctly keep them distinct.
Additional precompactness checks cover empty and three-point carriers,
the two language claims, and a genuinely infinite raw palette
`Int x ZMod 2` with finite effective group `ZMod 2`. Both the typed fixed
expansions and their actual native range are finite without a raw-palette
finiteness instance.

Evidence: `../preparation/affine-potential-independent-build.log`,
`../preparation/affine-potential-independent-check.lean`, and
`../preparation/affine-potential-independent-axioms.log`.
Precompactness evidence is in the corresponding
`../preparation/affine-precompactness-independent-build.log`,
`../preparation/affine-precompactness-independent-check.lean`, and
`../preparation/affine-precompactness-independent-axioms.log`.

| Module | SHA-256 |
| --- | --- |
| `Affine/LinearOperations.lean` | `9c6f92e4c44eccc318a384aa880c2629a035dd98831328b268a5761720a733fd` |
| `Affine/PotentialBasics.lean` | `2ddea5a29326299336d56967560a4d86b0926a9ceead50666e6053e13da8b6c4` |
| `Affine/Potential.lean` | `26823234d8123c6c5a6f3e59968f2f3764e3cdcae2db069495c9d6370f78b944` |
| `Affine/Precompactness.lean` | `f6d6896ee863fe3b164a459a183e8486cc3f56d4ef7dc5aeb3c60685be599c08` |
