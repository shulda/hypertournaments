# Independent small-arity and AP-to-SAP review, 2026-11-14

Source: `shulda/tex_hypertournaments` at
`919349e7eceed3c7fa0ed126a337c6fae6624704`,
`thm:constrained-classification` and the following unboundedness discussion.
Reviewed `LocalAmalgamationTransport.lean`, `SmallArityPalettes.lean`, and
`SmallArityClassification.lean` at the frozen hashes below. The reviewer
did not edit the three proof files. No unresolved mathematical or API
issue was found.

## Actual finite amalgams and overlap

`admissible_iff_of_palette_agree` compares allowed sets only at possible
indices, using the proved upper bound `localIndex_le_central`. It makes
no assumption that impossible indices are absent from either original
set.

`local_hasStrongAmalgamation_of_strong_span` transports an actual
`Hyper` on `FiniteStrongSpan.Carrier f g` to a finite ordinal by the
literal `Fintype.equivFin` equivalence. Both preserving embeddings are
composed with that same equivalence, and the tuple equalities explicitly
cancel its inverse before invoking the original preservation proofs.
Admissibility is transported along the inverse embedding. Commutation
uses the actual span commutation equation; the strong overlap clause
uses injectivity of the equivalence and `FiniteStrongSpan.overlap`.
No extra vertices or unintended identifications are introduced.

The source embeddings retain the ordinary `Preserves` interface.
They are not assumed to preserve auxiliary orders. Empty finite carriers
and an empty base are included. The unused admissibility premise for the
base in the span-to-class interface is harmless: the class definition
requires it, while the supplied stronger span construction needs only
the admissibility of the two sides.

`local_hasAP_of_hasStrongAmalgamation` forgets only the exact-overlap
clause and translates the same actual witness between the local-index
and omission interfaces. It does not silently identify ordinary and
strong amalgamation.

## The two and four valid small-arity palettes

The palette lemmas enumerate sets contained in `0..centralIndex n`
and containing the central index. For binary arity this yields exactly
`{1}` and `{0,1}`; for ternary arity it yields exactly `{2}`, `{0,2}`,
`{1,2}`, and `{0,1,2}`. Each proof splits membership of the noncentral
indices and proves equality of the entire allowed set.

The binary cases invoke the proved transitive-tournament construction
and unrestricted strong amalgamation. The ternary cases invoke,
respectively, actual cyclic strong amalgamation, the even/switching
construction, and the central-plus-next-central construction for the
last two palettes. `switchingAllowed_three` proves the exact equality
with `{0,2}`. Each selected construction returns the common prescribed
`FiniteStrongSpan.Carrier`, not an abstract amalgam provider.

The binary unrestricted case checks admissibility of the resulting
structure from the actual range bound on its local index. The ternary
central-plus-next-central calls discharge the actual two membership
premises for the displayed palettes. No low-arity construction is
obtained by applying a theorem outside its arity bounds.

## Phantom indices and the all-arity conclusion

`small_arity_central_strong_span` replaces an arbitrary original palette
`S` internally by `S ∩ Iic (centralIndex n)`. Its validity and central
membership are proved, both sides are translated by
`admissible_validize`, and the output is translated back to the original
palette. Thus the original API has no validity assumption.

`strong_span_of_hasAP_all_arities` makes the same internal replacement
in the higher-arity branch. It also transports ordinary AP by the proved
`hasAP_validize` before using `strong_span_of_hasAP`. The arithmetic
branch split proves the needed lower bound `4 ≤ n`; arities two and
three are handled by their actual constructions.

`unbounded_hasAP_iff_hasStrongAmalgamation` obtains central membership
from the proved `unboundedAdmissible_iff_central`, then invokes the
actual span construction and the finite-presentation transport. That
unboundedness equivalence has an actual finite Ramsey proof in the
empty language and a constant-canonical-sign sufficient construction;
it has no conditional Ramsey, AP, or central-membership provider.
The reverse implication is the ordinary forgetting map described above.

The final all-arity classification retains validity as a premise of the
exact palette criterion, matching the source statement. In the small
arities it proves AP from central membership; in the higher arities it
uses the already proved positive and negative classification. The
unbounded variant derives central membership from its stated
unboundedness premise.

## Validation and frozen snapshots

An independent three-target build passed with 1985 jobs. All fourteen
public theorem exports reported exactly `propext`, `Classical.choice`,
and `Quot.sound`. Explicit Lean examples passed for ordinary AP with
the phantom-containing binary palette `{1,42}`, the phantom-containing
cyclic ternary palette `{2,42}`, and the arity-four AP-to-SAP equivalence
with an arbitrary unbounded original palette. A scan of the three proof
files found no `sorry`, `admit`, custom axiom, `native_decide`, unsafe
declaration, or unresolved provider. Tactics used by these modules have
direct imports.

Evidence: `../preparation/small-arity-classification-independent-build.log`,
`../preparation/small-arity-classification-independent-check.lean`, and
`../preparation/small-arity-classification-independent-axioms.log`.

| Module | SHA-256 |
| --- | --- |
| `LocalAmalgamationTransport.lean` | `0ba5bba7062391cb8b065b7f02bc6fe3bbfb82ef0a343bf980eb4e701ad260b8` |
| `SmallArityPalettes.lean` | `da04ecdb23ef77fcb5d091745f6ee5d35d3454574766718b776258f20ad930cf` |
| `SmallArityClassification.lean` | `5604d56b3865f085c9880d3b821ebcc4693588cc9257c42ded495f488ed2da33` |
