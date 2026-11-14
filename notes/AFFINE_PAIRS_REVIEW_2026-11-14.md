# Independent affine foundations and pairs review, 2026-11-14

Source: `shulda/tex_hypertournaments` at
`919349e7eceed3c7fa0ed126a337c6fae6624704`, the final subsection,
`Further potential constructions`. Reviewed all eight frozen modules
listed below, including the ordered-extension and midpoint helpers on
which the ordering theorem depends. No blocking mathematical or API
issue was found. No reviewed proof source was modified.

## Involutions and ordered presentations

`Palette` requires only an involution. `Labelled` names actual labels of
injective tuples, and its swap law implies the full permutation law by
swap induction. Neither fixed-point-freeness nor palette nonemptiness is
introduced. In particular the trivial palette correctly models labels
fixed by every odd permutation. The finite-instance proof uses only the
injective projection to a finite function space when both carrier and
palette are finite.

`fromOrderedLabels` uses the sign of the actual sorting permutation.
The existing sorting and underlying-set lemmas prove its swap law, and
canonical recovery sorts every injective tuple and recovers it using the
inverse sorting permutation. Thus canonical checks establish equality
and preservation on every ordered tuple. No claim is limited to the
increasing representatives. The fallback in `canonicalTable` is explicit;
the foundational recovery results impose no hidden nonempty-palette
instance.

## Full native embeddings

`Labelled.Relation q t` requires injectivity and the actual label `q`.
All repeated-coordinate tuples satisfy none of the named label relations.
`preserves_iff_relation` proves both directions of the relation equivalence
for arbitrary tuples, deriving source injectivity in the reflection
direction. `pairNativeEmbedding` and `pairOrderedEmbedding` are therefore
full native embeddings, with reflection for every named lower and upper
label. The latter also preserves and reflects the strict linear order.
The converse embedding adapters recover both original intrinsic
preservation equations.

## Arbitrary relational Ramsey witnesses

The ambient witness supplied by the pinned
`CCO.UnaryHN.Native.allOrderedModels_ramsey` is an arbitrary relational
structure equipped with an actual linear order. The proof does not
silently assert that this witness has unique labels or satisfies a
palette involution.

Instead `uniqueLabel` selects the unique true label when one exists,
and uses its explicit fallback when there is no true label or several.
`decodeLabelled` reads this selector on canonical subsets and then
reconstructs an actual involution-labelled structure. A full encoded
source copy has exactly its original unique label at every increasing
tuple, by relation preservation and reflection. Consequently
`decodeLabelled_preserves` proves that every such copy survives decoding
on all injective tuples. Repeated-tuple reflection in the decoded native
structure follows from its actual `Labelled.Relation` definition.

`decodedPairEmbedding` retains the literal original vertex map and order.
Its compatibility with composition is proved by equality of those maps.
Pulling a colouring back through this decoder therefore transfers the
ambient Arrow theorem to the actual decoded pair, without any provider
premise about middle-copy correctness.

The actual signatures preserve the intended scopes:

| Endpoint | Hypotheses and quantifier scope |
| --- | --- |
| `exists_pair_ordered_ramsey_witness` | Every arity `r`; arbitrary nonempty palettes; finite source carriers; any finite nonempty colour type; returns an actual finite pair and Arrow. |
| `pair_ordered_ramsey` | The full freely ordered native pair class, with independent language, carrier, and colour universes; no finite-palette premise. |
| `exists_all_pair_order_host_with` | `r >= 2`; one fixed finite host and target order contain every free order of one given pair, retaining an anchor. |
| `exists_all_pair_models_order_host_with` | Adds finite palettes to obtain one fixed host for every pair on the specified finite source carrier and every order, retaining the anchor. |
| `pair_ordering_property` | `r >= 2`; one finite intrinsic target is selected before both source and target free orders; arbitrary nonempty palettes suffice. |

## Joint hosts and all source orders

Both independent arities amalgamate on the same literal
`FiniteStrongSpan.Carrier`. A compatible target linear order comes from
the proved ordered-span shuffle, while the intrinsic label embeddings
retain their original functions. The empty-base joint embedding uses a
genuine common empty pair; `r >= 2` ensures both named arities are positive.
Empty sides and an empty finite index family are covered explicitly.

Finite-family joint embedding retains the anchor at every induction step.
The all-order host enumerates the finite permutation type of the source,
then transports each requested source order through the actual
`orderChange` isomorphism. `pairOrderExpansionReindex` uses its inverse
map and proves cancellation on every tuple in both arities. For the
all-model host, finiteness of the two palettes is used exactly to make
the index type of all pairs on the fixed finite source finite. The host
is not chosen after the requested model or free order.

The free-labelled strong-span theorem is an imported dependency and has
its own separate review; this note does not replace that review.

## One edge type controls every original pair

`extendOrdered` preserves the entire original pair and gives every
genuinely new increasing tuple the chosen fallback label. For `r = 2`,
the low binary edge is checked on its actual increasing canonical tuple;
the reverse follows from the palette involution. For `r > 2`, no lower
tuple exists on two points, and the high arity is always absent there.
Thus the selected edge embeddings are full embeddings also in the
binary lower-arity case and for involution-fixed labels.

`OrderWitnessCarrier` inserts an actual fresh point for every strict old
pair `(a,b)`. The finite rank construction puts this point strictly
between its two endpoints and preserves the order of all old vertices.
For each old pair, both halves of the inserted chain have the same
chosen ordered edge type. `pairOrderWitness_homogeneity` compares both
halves for every old pair to one fixed baseline edge. The common colour
therefore makes all old pairs increasing, or all decreasing, in the new
target order. Injectivity turns the two false comparisons into strict
reverse comparisons. If there is no old strict pair, monotonicity is
correctly vacuous.

The final Ramsey step homogenizes all embeddings of that edge model,
so it supplies exactly this universal homogeneity premise. It does not
only control selected pairs. The all-order host then supplies the
requested source order, or its reverse in the decreasing case. The same
intrinsic embedding is retained when its auxiliary orders are changed.
The two-point source is lifted into the carrier universe explicitly,
avoiding a hidden restriction to `Type 0`.

## Validation and frozen snapshots

An independent eight-target build passed (1239 jobs). Nineteen focused
axiom checks covering foundations, full embeddings, decoder transfer,
Ramsey, both universal hosts, ordered extensions, midpoint geometry,
homogeneity, and ordering reported exactly `propext`, `Classical.choice`,
and `Quot.sound`. No reviewed module emitted a new warning; dependency
warnings were replayed by Lake.

Seven additional Lean examples verified absent-label fallback,
multiple-label fallback, actual decoding into a fixed-point palette,
repeated-tuple falsity, Ramsey with an infinite fixed-label palette and
separate palette/carrier/colour universes, an all-model/all-order host
for a nontrivial three-point source in `Type 1`, and the empty-source
ordering property with an infinite fixed-label palette. The reviewed
sources contain no `sorry`, `admit`, custom axiom, `native_decide`, or
unsafe declaration.

Evidence: `../preparation/affine-pairs-independent-build.log`,
`../preparation/affine-pairs-independent-check.lean`, and
`../preparation/affine-pairs-independent-axioms.log`.

| Module | SHA-256 |
| --- | --- |
| `Basic.lean` | `b360a15d1d0cd5869f1b86f58d206b2a7c418b445300f4a4d42b2c79ea2adcf0` |
| `OrderedLabels.lean` | `55ff4f214aebe63bac4b3f324a4ca220aee3390c585024e77f2c0b2855762e04` |
| `PairLanguage.lean` | `0863d5a88ec7153d38c1c4dcb2429836a1b595fe8883d21fbb6f4a16abd6e893` |
| `PairRamsey.lean` | `e33f870589f713703388ad4d18e191db983b1e55c4b42e5b2788a08168b6fd1d` |
| `PairOrderHost.lean` | `87a9d08b1ecae345e2779c2de79239f517a55e29ce36337f04370cf12fd1b3d5` |
| `OrderedExtension.lean` | `866286aef18ac3965f07bca32cd72e778a418674275dbc42430a50e812553e9b` |
| `PairOrderWitness.lean` | `2accc73c804ac19a7b115b78fa29549f870d962f1afc35169e3b998eba98d083` |
| `PairOrdering.lean` | `18bf5d91c6d0d791c634503819c8e3e991f2988c8b6e7f35b08ef489085b2563` |
