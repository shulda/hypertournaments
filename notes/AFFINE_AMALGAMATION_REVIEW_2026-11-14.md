# Independent affine amalgamation review — 2026-11-14

Reviewed the frozen `Affine/LabelledAmalgamation.lean` and
`Affine/Amalgamation.lean` against article commit
`919349e7eceed3c7fa0ed126a337c6fae6624704`, final subsection
“Further potential constructions”. The review found no mathematical or
interface gap. The author added the direct `Mathlib.Tactic.SplitIfs` import
requested by the import review; no author proof was changed. The final
snapshots below include this import-only cleanup.

The inspected dependencies include `Data`, `FiberCoding`, `ExpansionCoding`,
`Potential`, `PotentialBasics`, `GaugeAlignment`, and `LinearOperations`.
The separately reviewed signed exactness and permutation results are used
through their actual proved statements.

## Actual labelled strong amalgams

`labelled_amalgam_on` assumes agreement on every pair of actual ordered
tuples whose images coincide. It chooses one order on the target, pulls
it back to the two sides, and sets each canonical label from the left
source if possible, otherwise from the right source, otherwise to the
supplied fallback. Agreement proves that the priority does not affect
labels on the overlap. Canonical recovery then gives preservation on all
ordered injective tuples, including odd reorderings and involution-fixed
labels. No source order is an input of the resulting preservation statement.

`labelled_strong_span` applies this to the literal
`FiniteStrongSpan.Carrier f g`. Equality of image tuples yields a tuple in
the actual common base, coordinate by coordinate using
`FiniteStrongSpan.overlap`. Its injectivity follows from the original
tuple injection. Preservation from that base proves the required label
agreement.

Both original source injections are retained as
`FiniteStrongSpan.left f g` and `FiniteStrongSpan.right f g`.
The existing `commutes`, `overlap`, and `covers` theorems for this carrier
therefore supply the prescribed exact intersection and exact union.
The endpoint needs only `Finite B`, `Finite C`, and a nonempty palette for
mixed-tuple fallback values. It does not require a finite palette, a chosen
base vertex, or a separate `Finite A` instance.

Arity zero is also valid: the empty source tuple still has its common
base label, and preservation over the base forces the two side labels
to agree. Coordinate choice over `Fin 0` introduces no inhabitance
assumption on the base. Empty bases and empty sides are included.

## Potential expansions and exact raw labels

`expanded_strong_span` first chooses one order on the exact union carrier.
The side and base orders are induced along the original maps; the
commutativity equation of the exact carrier makes both original base
maps increasing. These orders are used only to select compatible source
codes. They are absent from the theorem hypotheses and conclusion.

The lower potentials and the upper oriented codes are amalgamated
independently on the same carrier. `Data.decodePair_preserves` transports
these actual injections to decoded expansions. The source identities
`Expansion.decode_toCodePair` recover the whole original raw `Q`-labelled
structure and potential, rather than just the effective `G`-labels.

In particular, the argument never infers equality of raw labels from
equality under `d.effective`. The fiber decoder has a section on every
actual fiber, handles the raw palette involution, and retains duplicate
fiber codes and fixed raw labels. Surjectivity provides a fallback in
each fiber and implies `Nonempty Q`; injectivity is never assumed.

The offset premise is exactly
`Even (r + 1) -> d.offset = 0`, where `r + 1` is the upper arity.
It matches the article's zero-offset requirement for even upper arity.
The theorem is proved for every `r`; it has no `Finite Q`, `Finite G`,
source-order, or nonempty-carrier premise.

## Closed reducts and signed gauge alignment

`closed_strong_span` has the source range `2 <= r`, hence upper arity at
least three. Actual side potentials are obtained from the finite-carrier
closedness/exactness theorem. The base potential is the pullback of the
left potential along the given `f`; actual raw preservation identifies
its effective coboundary with that on the right base.

The right potential is then aligned to this prescribed base potential
by `IsPotential.exists_aligned`. This uses an ordinary signed lower
alternating gauge, extended by zero outside the original image of `g`.
Its coboundary has exactly the old source values. Adding it to the right
affine potential retains both the affine swap law and the original
effective coboundary, by the signed square-zero identity. The resulting
expanded span uses the original maps, and its raw reduct is closed.

The alignment has no root, order, nonempty-base, or finite-group premise.
Only the side carriers need be finite in this endpoint; no extra
`Finite A`, `Finite Q`, or `Finite G` hypothesis is introduced. The
article's strong-amalgamation assertion for finite closed reducts and
their actual potential expansions is therefore discharged by these
statements.

## Independent verification

Using Lean 4.34.1 and the committed manifest:

```
lake build Hypertournaments.Affine.Amalgamation
lake env lean --stdin
```

The independent target build passed (1142 jobs), with no warnings from
the two reviewed source modules. Local evidence is in
`../preparation/affine-amalgamation-independent-build.log` and
`../preparation/affine-amalgamation-independent-check.log`.

The separate check elaborated a genuinely noninjective effective map
`Z x Bool -> Z`, projection onto the first coordinate, with raw involution
`(g,b) |-> (-g,b)`. The two distinct raw fixed labels `(0,false)` and
`(0,true)` have the same effective label. Both the expanded and closed
amalgamation endpoints over an empty base retained these different raw
labels on actual three-tuples in their two five-vertex sides. This also
checks infinite raw and effective palettes and nonvacuous side closedness.
A separate arity-zero generic span on empty carriers elaborated as well.

Each selected endpoint reports exactly
`[propext, Classical.choice, Quot.sound]`:

* `labelled_amalgam_on`
* `labelled_strong_span`
* `expanded_strong_span`
* `closed_strong_span`
* `IsPotential.exists_aligned`
* `Data.decodePair_preserves`
* `Expansion.decode_toCodePair`

The pinned `axiom-audit` executable also checked every declaration defined
in the two reviewed modules (8 and 3 declarations, including private and
generated declarations). Both complete module audits passed with exactly
the same three allowed axioms. Their receipts are
`../preparation/affine-labelled-amalgamation-independent-audit.json` and
`../preparation/affine-amalgamation-independent-audit.json`.

Whole-project facade coverage, complete project auditing, and proposed-commit
CI are separate integration checks.

## Final reviewed SHA-256

| File | SHA-256 |
| --- | --- |
| `Hypertournaments/Affine/LabelledAmalgamation.lean` | `155840562375439876c6d21715d9668ff0cb7e1cc99cfafd1d709e5d65c73aaf` |
| `Hypertournaments/Affine/Amalgamation.lean` | `8c6a4f205250e36902e907b3681a7579ad05286eecb8aa0f34d23cded2c29e7c` |
