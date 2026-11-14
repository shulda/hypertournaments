# Independent finite-structure and P9 review, 2026-11-14

Reviewed the frozen `FiveConstrained/CertificateStructures.lean`, `P9.lean`,
`P9Consequences.lean`, and `Unbounded.lean`, which were written by other
agents. Inspected `Mask.lean` as their common semantic dependency; its
separate catalogue-agent review remains independently applicable. No
reviewed production proof was edited for this review.

No blocking mathematical or Lean-interface issue was found.

The mathematical comparison used the uploaded November technical note,
SHA-256 `a06eb1ae0377e798491354faa95357501046f79c5eaa2d482adcfeef02d412d7`,
and the original July classification supplement,
SHA-256 `d15fbb89b7e22c1cde1402e1ce417fd74566dd10d38d145b355d6ec9cf9bbcb3`.
The original pair-cancelling SAP/Ramsey/ordering interfaces were read at
their actual theorem signatures.

## Finite masks and the size-nine boundary

`orientAt` has exactly the six parity cases for distinct ternary
coordinates. Its values on repeated coordinates are irrelevant because
`maskHyper` accepts injective tuples only. Each of the three transposition
laws is proved, and the resulting object is the original `Hyper`, rather
than a separate finite-table surrogate.

`preserves_iff_triples` assumes increasing source triples only; its target
vertex map is an arbitrary injection. The existing canonical-recovery
theorem supplies preservation on all reordered tuples. The bridge
`maskHyper_fromOrderedSigns_orient` also identifies the direct evaluator
with the pre-existing canonical sign-table construction on every tuple.

`maskOfHyper` is operationally defined at every cardinality, but its
advertised recovery theorem explicitly requires `n <= 9`. The finite
lookup theorem quantifies over `Fin 10`, hence checks precisely sizes zero
through nine. It proves both the rank bound and the correct inverse lookup
on every increasing triple. This is sufficient for every retained
certificate: base size is at most seven, its sides have at most eight
vertices, and its canonical union has at most nine. No unproved general
rank-enumeration claim beyond that bound enters the certificates.

## Actual certificate structures and ordinary-AP identifications

`baseHyper` and both `sideHyper` objects realize the literal prescribed
base and pair-link tables. `base_side` preserves every oriented tuple on
the common base. The joint bit rule has three exhaustive cases on an
increasing triple: contained in the left side, contained in the right
side and using its added point, or containing both added points. The two
side prescriptions agree on the old base.

`joint_left` and `joint_right` retain the original canonical inclusions;
they do not replace them by unspecified isomorphic embeddings.
`mixedTuple` is exactly `(a,left,right)` in increasing order, so
`mixedMask` packs precisely the still-undetermined orientations. The
identity `joint_recovery` applies to every intrinsic joint preserving both
sides, reads its own mixed mask, and recovers its orientations on all
ordered injective tuples. Its proof makes no finiteness-search or
surjectivity assumption about a later ambient amalgam.

The integer inequality of the link masks is used carefully. The
`side_disagree` theorem additionally assumes the two actual bit-width
bounds and the verified base-size bound. Its proof obtains a differing
bit below the pair-mask width and realizes that bit by an actual
increasing pair. Thus it proves real orientation disagreement between the
two sides, which excludes identifying their added vertices in an ordinary
amalgam. High unused integer bits cannot create spurious disagreement.

## P9 and the complete positive consequences

`p9` is literally mask 41. A separate kernel-checked review example reads
its ten increasing triples and confirms that exactly positions 0, 3, and
5 are true: `012,023,034` in the July convention. The November note uses
the opposite names for the two raw signs; the code consistently treats
the stored bits as actual Boolean orientations.

The nonconstant-pair calculation quantifies over every ordered pair of
distinct vertices and supplies two vertices outside that pair with
different actual orientations. The `PairCancelling` proof also quantifies
over every auxiliary linear order. In ternary arity the ordered tail has
only one coordinate, and the proof explicitly shows that its monotonicity
condition is vacuous. It does not check only one selected order.

`p9Family` contains the single fixed presentation at cardinality five.
Nevertheless `Omits` quantifies over arbitrary vertex injections, so the
proved `omits_p9Family_iff` is exactly omission of every induced isomorphic
copy on any ambient carrier, including infinite or empty carriers.

Every source instance of the general pair-cancelling theorems is
discharged. `p9_hasStrongAmalgamation` has no provider premise, and
`p9_strong_span` uses the existing exact-overlap carrier with the given
side injections. Empty bases and empty sides are permitted.

`p9_ordered_ramsey` and the explicit-witness wrapper retain the full native
Ramsey arrow for intrinsic hypertournaments with freely chosen vertex
orders. The color type is any finite nonempty type; neither source nor
target carrier is assumed nonempty. The constructed witness is finite and
actually omits P9. The ordering-property wrapper chooses one finite
underlying target before quantifying over both subsequently chosen free
linear orders, as required by the full ordering property.

## Unboundedness is an actual structural statement

The general constrained-class equivalence is

```lean
(constrainedClass four five).Unbounded ↔
  four.testBit 2 = true ∧ five.testBit 0 = true
```

Necessity uses actual finite Ramsey in the empty language and hereditary
membership to obtain a constant canonical-sign packet. The two constant
five-packets have masks 0 and 1023, both recognized as P0. The analogous
four-packet has the actual old local index 2. Sufficiency constructs an
actual constant-sign `Hyper` at every requested finite cardinality and
checks both original predicates. No AP, consistency, palette-size bound,
or external Ramsey hypothesis is introduced.

The normalized equivalence then discharges the four-condition through
P0's proved support. It remains valid even if the input integer palette
has irrelevant higher bits.

## Validation and frozen source hashes

A targeted four-root build passed, 1688 jobs. The independent endpoint
file `../preparation/FiveMaskPositiveReviewCheck.lean` also passed. It
checks concrete size-nine mask recovery, generic joint recovery, the
three specified positive P9 bits, omission on the carrier `Nat`, and the
complete normalized-unboundedness equivalence. Fourteen selected axiom
prints use only `propext`, `Classical.choice`, and `Quot.sound`.

Logs are `../preparation/five-mask-positive-review-build.log` and
`../preparation/FiveMaskPositiveReviewCheck.log`. These focused checks
supplement the integration-wide build and complete defining-module audit.

| Reviewed module | SHA-256 |
| --- | --- |
| `FiveConstrained/Mask.lean` | `46c719592a42d7208adc3b86b1e0d7f1eb27367697ebc600b2dcde4b4cd20eae` |
| `FiveConstrained/CertificateStructures.lean` | `9e3a7ffb1a28283662adc32e173a0462cb29e469b135c3bb5bb267248a2577d1` |
| `FiveConstrained/P9.lean` | `e959c20654fbec89970bccd63a73f35e6b800864015bb1294573efecc3721237` |
| `FiveConstrained/P9Consequences.lean` | `e2c32692ce245ef84eeb86fd31da93ed070f3e08d01016168255b03fca875afe` |
| `FiveConstrained/Unbounded.lean` | `595ed11dada09f80e7039ae38bbdd74c1dbc20b265b1eb6604c3be9967e3b646` |
