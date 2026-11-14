# Independent positive-classification review, 2026-11-14

Reviewed `LocalPairCancellation.lean`, `LocalForbiddenFamily.lean`, and
`PositiveClassification.lean` against `lem:local-types` and the
classification integration in `shulda/tex_hypertournaments` at
`919349e7eceed3c7fa0ed126a337c6fae6624704`. The recovered proof preparation
provides the expanded local-cutoff argument and the exact intended final
AP interface. Relevant definitions and input signatures were also checked
in `PairCancellation`, `GeneralLocalIndexInvariant`, `PartialHyper`,
`PairAmalgamation`, `EvenAmalgamation`, `NegativeClassification`,
`LocalTypes`, and `Amalgamation`.

No blocking mathematical or API issue was found. The package proves the
positive alternatives and combines them with the existing unconditional
negative theorem to give the ordinary-AP classification with its original
validity and central-type premises.

## Local cutoff and the pair-cancelling quantifiers

`pairCancelling_of_localIndex_le` proves that an `(n+1)`-vertex packet of
local index at most `centralIndex n - 2` is pair-cancelling, for `3 ≤ n`.
It proves the sufficient cutoff direction needed by positive amalgamation.
The reverse direction of the article's local-types equivalence is a
separate result and is not implicitly assumed here.
Its completed package is reviewed in
`LOCAL_PAIR_CANCELLATION_REVIEW_2026-11-14.md`.

The proof handles every auxiliary linear order and every ordered pair of
distinct vertices, exactly as quantified in `PairCancelling`. It places
that pair first and lists the remaining vertices increasingly in the
chosen auxiliary order. The two distinguished vertices need not themselves
be increasing. Deleting any tail vertex gives a genuine `IsPairLink` tuple
with that same pair and tail order.

If those links have constant raw orientation, their `n-1` normalized facet
values alternate. Each Boolean value then occurs at least
`floor((n-1)/2) = centralIndex n - 1` times in the full packet, regardless
of the first two facet values. Thus the local index is at least `q-1`,
contradicting the assumed cutoff `q-2`. Full coordinate-permutation
invariance transports the index back to the identity packet. No
order-preservation or unsupported invariance of the raw orientation is
used in that transport.

The arity hypothesis ensures `q ≥ 2`, so natural-number subtraction does
not erase the required strict gap. In particular, the proof includes
`n = 3`, where the cutoff is exactly zero. The arity and carrier-size
conditions inside `PairCancelling` are proved, rather than omitted from
the conclusion.

## Exact omission bridge on arbitrary carriers

`localForbiddenFamily n S` consists of all nonadmissible intrinsic packets
on precisely `n+1` vertices. It does not select only particular ordered
presentations or a proper subset of the forbidden local indices.

`packet_admissible_iff_localIndex_mem` correctly tests a full packet by its
identity tuple: every injection from that finite carrier to itself is a
permutation, and local index is invariant under all such permutations.

`omits_localForbiddenFamily_iff_admissible` holds for every ambient
carrier, with no finiteness, order, or nonemptiness assumption. A bad
ambient packet pulls back to a forbidden finite structure and embeds back
by its actual tuple injection. Conversely, an orientation-preserving
injection of a forbidden packet would inherit admissibility from the
ambient structure, a contradiction. `Preserves` compares every injective
ordered tuple, so these are genuine induced orientation copies; the proof
does not replace them with a weaker homomorphism notion.

If the central and next-central indices are allowed, every forbidden
packet has index at most `q-2`, since all local indices are at most `q`.
`localForbiddenFamily_pairCancelling` therefore supplies the actual
pair-cancelling proof for every member of this family. This argument
correctly permits phantom allowed indices above `q`; none can change a
packet's admissibility. It does not need `ValidTypes`.

## Actual strong amalgams and the original ordinary AP

`central_next_strong_span` applies the already proved pair-cancelling
completion/amalgamation theorem to this explicit forbidden family, then
uses the exact omission equivalence to return to `Admissible S`.
There is no remaining completion-provider or family-PC premise.

The input carriers are arbitrary finite types, including empty sides and
empty bases, and the input maps are arbitrary orientation-preserving
vertex injections. Only the side carriers require finiteness explicitly;
the base embeds into either side. The witness lives on the literal
`FiniteStrongSpan.Carrier f g`, and uses its fixed `left` and `right`
injections. Consequently `FiniteStrongSpan.commutes`, `overlap`, and
`covers` give exactly the original common base, no unintended additional
identifications, and no extra vertices. Completion changes only the
previously unprescribed orientations on that carrier.

`central_next_ordered_strong_span` extends arbitrary compatible free side
orders on those same vertex maps. Order is additional data and does not
alter the meaning of `Preserves` or impose an order condition on the
unordered result.

`central_next_hasAP` forgets the exact-overlap condition from the actual
finite `HasStrongAmalgamation` witness. Its conclusion is the original
`HasAP n S`: arbitrary finite-ordinal inputs, arbitrary orientation
embeddings, an admissible finite witness, preservation of both sides, and
commutation over the base.

The exceptional odd switching alternative uses the independently proved
`switching_strong_span` and `switching_hasAP`. Its all-odd bridge to even
hypertournaments and its actual potential amalgamation are not new
premises of this package. Both positive branches therefore have strong
amalgamation of the intended class.

## Exact classification premises

The final public theorem has precisely the required shape:

```
amalgamation_classification (n : ℕ) (hn : 4 ≤ n) (S : Set ℕ)
    (hvalid : ValidTypes n S) (hcentral : centralIndex n ∈ S) :
  HasAP n S ↔ NecessaryAlternatives n S
```

Here the right side is exactly
`q-1 ∈ S ∨ (Odd n ∧ S = switchingAllowed n)`. The forward implication
uses the existing unconditional negative classification, with no odd
exceptional-family premise remaining. The reverse implication discharges
both alternatives with the constructed positive AP results.

Validity remains necessary to this exact statement about the set `S`:
phantom indices do not affect the class but would affect equality with
`switchingAllowed n`. Central membership is also retained explicitly.
The package does not silently replace it by unboundedness or claim a
finite-Ramsey-dependent equivalence with unboundedness.

`strong_span_of_hasAP` is correctly limited to this classified setting
(`n ≥ 4`, valid indices, central membership). It obtains a positive
alternative from ordinary AP and constructs the corresponding strong
span. It does not assert that ordinary AP universally implies strong AP.

## Independent verification and frozen snapshots

An independent targeted build of all three modules passed, with 1862 jobs.
A standalone Lean check inspected eleven principal exports and verified:

- the omission equivalence on the infinite ambient carrier `ℕ`;
- the local cutoff at `n=3` and local index zero;
- the final equivalence expanded to the exact original `HasAP` type and
  the explicit source alternatives.

All eleven selected `#print axioms` results contained exactly
`propext`, `Classical.choice`, and `Quot.sound`. The reviewed files contain
no proof placeholders or native proof shortcuts. These targeted checks
supplement the project-wide audit performed separately by integration.

Local reproduction and evidence:

```
lake build Hypertournaments.LocalPairCancellation \
  Hypertournaments.LocalForbiddenFamily Hypertournaments.PositiveClassification
lake env lean ../preparation/PositiveClassificationReviewCheck.lean
```

The logs are
`../preparation/evidence/positive-classification-independent-build.log` and
`../preparation/evidence/positive-classification-independent-exports.log`.
The reviewed frozen snapshots have these SHA-256 hashes:

| Module | SHA-256 |
| --- | --- |
| `LocalPairCancellation.lean` | `403a75f600a03e2a1f847b00ebeea32950abd35b06b1e63e5fa95794fc2d68fc` |
| `LocalForbiddenFamily.lean` | `e63e4f3398d1f55b97ea6ec640cf2d01c10849209635e0a2109b45f0af28710d` |
| `PositiveClassification.lean` | `7f35c747e4a2dbc9e8c074b6ba73faa027332f31bd354bed53da87a1389f049a` |

No proof files were changed for this review. The separate five-constrained
ternary classification remains outside its scope.

## Additional local-class Ramsey and ordering wrappers

The subsequently frozen `LocalClassRamsey.lean` was also reviewed. Both
wrappers require central and next-central membership and use the proved
`localForbiddenFamily_pairCancelling` input. They translate admissibility
to omission for the input structures and translate the actual output back
to `Admissible S`; the returned witnesses therefore belong to the original
local-index class, rather than merely an unspecified omission class.

`exists_local_class_ramsey_witness` retains the full native ordered
relational `Structure.Arrow`: every coloring of embeddings of the source
into the witness has an embedding of the target on whose source
subembeddings the color is constant. Its orders are arbitrary free vertex
orders, its color palette is any finite nonempty type, and its witness is
finite and explicitly admissible.

`local_class_ordering_property` chooses the underlying finite admissible
target before quantifying over both source and target linear orders.
Thus it has the full ordering-property quantifier order. Neither wrapper
adds a nonempty-source premise or a validity condition on phantom allowed
indices.

These are results for the central/next-central positive branch only.
They do not assert free-order Ramsey for the exceptional switching class;
the named-potential expansion and its Ramsey theorem are different
statements. Both signatures were independently checked after the module
compiled. The local log is
`../preparation/evidence/local-class-ramsey-signature-review.log`.

The reviewed SHA-256 of `LocalClassRamsey.lean` is
`135cbef36e61b876438833ef968e06fb275930e76cc905ddc3a52664c1ff2bf2`.
