# Local classification and elementary EPPA group inputs

## Source and boundary

Article source: `shulda/tex_hypertournaments` at
`919349e7eceed3c7fa0ed126a337c6fae6624704`, especially
`lem:local-type-isomorphism`, `lem:local-types`,
`thm:constrained-classification`, `lem:klein-centralizer-generation`, and
the preparatory lemmas for `prop:higharity-eppa-obstruction`.
The expanded proof preparation supplies the elementary Sylow/Klein route.

This package extends main `25e646469f3e0b6df77ad9c884440f62c815880d`.
The shared `Hyper`, `Preserves`, local-index palette and ordinary `HasAP`
interfaces, compiler/dependency pins, and immutable Ramsey provider snapshot
are retained. No private manuscript is copied into the repository.

## Complete local types

`LocalTypeRealization` constructs an actual orientation from **any** normalized
Boolean facet packet. Each prescribed canonical facet is recovered literally.
The threshold packet supplies `localTypeRepresentative n d` and realizes
every `d ≤ centralIndex n`, without an arity restriction.

`NormalizedPacketSign` proves the exact permutation law: normalized entries
are permuted and complemented exactly when the coordinate permutation is
odd. `FacetOrientationRecovery` proves that preserving the actual facets
preserves every ordered injective n-tuple.

`localIndex_eq_iff_exists_preserving_perm` in `LocalTypeIsomorphism.lean`,
within the `Hypertournaments` namespace, proves completeness for n at least two. Equal
minority counts match the Boolean packets up to complement. If a matching
permutation has the wrong parity, a transposition of two equal-colored
entries repairs it without changing the matched packet. Such a pair exists
because the packet has at least three entries. The final witness is an
actual orientation-preserving vertex permutation.

The n≥2 bound is substantive: the two constant unary orientations on two
vertices have the same minority index and are not isomorphic. The exact
sign law and realization results themselves cover those smaller arities.

## Exact pair-cancellation cutoff

`pairCancelling_iff_localIndex_le hn A` proves, for n≥3 and a packet on
`Fin (n+1)`,

```
PairCancelling A ↔ localIndex A (Function.Embedding.refl _) ≤ centralIndex n - 2.
```

The forward cutoff construction handles every original auxiliary order and
ordered pair of distinct vertices. A constant link gives an alternating
normalized tail, forcing index at least q-1. Conversely, a packet with index
at least q-1 can be permuted to have a balanced alternating tail. The global
complement in the permutation law is absorbed into its constant raw link.
`LocalConstantLink` constructs the actual auxiliary order and checks every
possible pair link, not just one preferred enumeration. Arity three is included.

## Actual admissible classes and ordinary AP

`localForbiddenFamily n S` consists exactly of the nonadmissible packets on
n+1 vertices. `omits_localForbiddenFamily_iff_admissible` holds on every
carrier, including empty and infinite carriers. Its embeddings are the
original arbitrary orientation-preserving injections.

When both central indices belong to S, every forbidden packet satisfies the
proved cutoff. The same-carrier PC completion therefore gives actual strong
amalgams for the admissible class, with compatible free orders as well.
`LocalClassRamsey` returns actual admissible Ramsey witnesses and full
ordering-property witnesses for this branch. It does not apply this
free-order Ramsey argument to the exceptional switching branch.

`amalgamation_classification` closes both directions of the previous negative
criterion for n≥4, under its exact validity and central-membership premises:

```
HasAP n S ↔ NecessaryAlternatives n S.
```

Both alternatives have strong amalgams on the exact-overlap carrier.
`strong_span_of_hasAP` derives these from ordinary AP in the classified setting.

## Unboundedness is discharged

`UnboundedAdmissible n S` means admissible finite structures exist in
arbitrarily large cardinalities. `unboundedAdmissible_iff_central` proves
its equivalence with central membership in **every** arity, without validity
or AP premises.

For sufficiency, constant canonical signs give explicit structures of every
finite size. For necessity, the proved Ramsey theorem for the empty base
language with a free linear order is applied to orders of sizes n and n+1.
Color an n-point embedding by the actual orientation. The genuine ordered
facet embeddings give a constant raw packet, whose local index is central.
No Ramsey assumption about the admissible class is introduced.

`UnboundedClassification` consequently exports both the AP iff under actual
unboundedness and a single iff characterizing unbounded AP classes among
valid palettes. Bounded classes are not silently identified with this setting.

## Elementary centralizer generation

The article's group input is proved without invoking an external
coprime-action generation theorem. `KleinCentralizerGeneration` supplies
source-exact saturation and generation statements under Mathlib's standard
`IsKleinFour E` mixin. Its generators and p-group facts are proved internally.

The underlying `CentralizerSaturation` works more generally for a 2-group
containing the displayed independent commuting involutions; the acting
2-group need not be finite. For a proper invariant H in an odd finite K,
choose a prime divisor of its index and an invariant Sylow P. The subgroup
J=P∩H is proper. The finite p-group normalizer condition gives
J strictly below its normalizer N. All restricted actions and the action on
the actual nontrivial quotient N/J are constructed in `StableGroupAction`.

`KleinFixedPoint` supplies a nonidentity fixed coset for some nontrivial
involutive scalar. `OddCosetFixedPoint` lifts it to a fixed representative;
this lemma does not assume its odd subgroup normal or the ambient group finite.
Saturation puts the representative in H∩P=J, contradicting its coset.
The subgroup generated by all nonidentity fixed elements is invariant by
conjugating the acting scalar, so saturation proves generation.

`InvariantSylow` discharges the fixed-Sylow input by the p-group fixed-point
theorem and the actual odd number of Sylow subgroups. `KleinQuotientLift`
proves that a Sylow subgroup maps isomorphically onto a p-group quotient
when the kernel has prime-to-p order. In particular, an order-four quotient
with odd kernel has a literal Sylow restriction equivalence. This stronger
lifting statement also covers cyclic order four; the Klein hypothesis is
supplied separately where the generation theorem is used. No general
Schur-Zassenhaus theorem is required.

## Actual automorphisms and EPPA foundations

`Automorphism` defines the actual orientation-preserving subgroup of vertex
permutations, its faithful action and standard pointwise stabilizers.
`OddStabilizer` proves that an involution fixing an (n-2)-tuple is identity;
on a moved pair plus the fixed tuple, preservation contradicts the swap law.
Cauchy's theorem then gives odd order of the actual pointwise stabilizer
of any finite set with at least n-2 vertices. It covers every finite
n-hypertournament for n≥2, including empty and binary cases.

`EPPA` defines induced partial automorphisms on subsets and ordinary finite
witnesses. Extensions are chosen separately for each partial automorphism;
there is no coherence requirement. Witnesses have finite entire target
carriers. Conjugation transports their actual automorphisms to any equivalent
finite carrier, including the finite-ordinal interface. An unrestricted
finite-witness obstruction excludes EPPA in every omission class containing it.

The concrete local high-arity EPPA obstruction, its class-level consequences,
and the one-arity-lower transfer remain subsequent theorem obligations.
This package proves their group inputs, automorphism/stabilizer facts and
witness interfaces. Infinite antichain and Fraisse corollaries require their
own additional infrastructure. Five-constrained ternary classification
remains postponed.

## Validation

Independent source-linked mathematical and API reviews are in:

- `POSITIVE_CLASSIFICATION_REVIEW_2026-11-14.md`;
- `LOCAL_PAIR_CANCELLATION_REVIEW_2026-11-14.md`;
- `CENTRAL_UNBOUNDED_REVIEW_2026-11-14.md`;
- `CENTRALIZER_SATURATION_REVIEW_2026-11-14.md`;
- `ODD_STABILIZER_REVIEW_2026-11-14.md`;
- `EPPA_FOUNDATIONS_REVIEW_2026-11-14.md`;
- `SOURCE_INSTANCES_REVIEW_2026-11-14.md`.

The machine-readable receipt is
`verification/classification_groups_2026-11-14.json`. It pins the full Lean
source/configuration inputs and records complete defining-module audits for
Hypertournaments, CCO, PartiteConstruction and SuccessorTree. The only allowed
axioms are `propext`, `Classical.choice` and `Quot.sound`. CI checks the exact
proposed head; PR metadata records both pre- and post-merge CI evidence.
