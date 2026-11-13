# Independent even-amalgamation review, 2026-11-13

Reviewed `EvenPotentialGauge.lean`, `PotentialAmalgamation.lean`, and
`EvenAmalgamation.lean` against the potential/switching lemma and
`prop:potential-SAP` in `shulda/tex_hypertournaments` at
`919349e7eceed3c7fa0ed126a337c6fae6624704`, using section 4 of the prepared
formalization source. The review also followed their mathematical interfaces
in `EvenPotential`, `HyperCoboundary`, `EvenSwitching`,
`CanonicalOrientationRecovery`, `FiniteStrongSpan`, and `Amalgamation`.

No blocking mathematical or API issue was found. The results cover every
odd upper arity at least three, including upper arity three and its binary
potential. They do not require a nonempty base, ordered underlying vertex
injections, or an unproved amalgamation/completion provider.

## Gauge alignment

`IsPotential` is the actual unsigned coboundary equation on every injective
ordered tuple. The gauge result is consequently about the intrinsic upper
orientation, rather than only its increasing sign table.

- `IsPotential.intrinsic_gauge` proves the gauge equation on all tuples of an
  arbitrary finite carrier. The canonical proof is transported through an
  equivalence with a finite ordinal, and equality on canonical tuples is
  recovered intrinsically by alternation. No order is imposed on the
  original carrier.
- `extendGauge` agrees with the original scalar cochain on the image of the
  base injection and is zero on subsets containing an outside vertex.
  `coboundary_extendGauge_map` correctly asserts naturality after restricting
  back to that image. It does not assert that the global coboundary vanishes
  away from the image, which would be false.
- `Hyper.cochainShift` adds a symmetric support function, so the shifted
  lower orientation is still alternating. Shifting by the coboundary of the
  extended gauge leaves its actual tuple coboundary unchanged by the proved
  identity `δ² = 0`.
- `IsPotential.exists_aligned` preserves a prescribed potential along any
  vertex injection from a finite base. Its use of
  `preserves_of_canonical` does not require the injection to be increasing:
  the comparison is with the target pulled back to the ordered source.
  The final conclusion therefore preserves all ordered tuples, including
  those whose images are not increasing in any auxiliary target order.
- The positive-degree hypothesis `0 < r` is explicit. Empty carriers have
  no positive-cardinality supports, so the zero gauge handles that case
  before any vertex is chosen. This avoids the invalid degree-zero claim:
  two distinct zero-arity orientations on the empty carrier can be
  potentials of the same unary orientation but cannot differ by a scalar
  coboundary on the empty support. Every amalgamation use has `2 ≤ r`.

## Expanded and reduct amalgamation

`potential_strong_span` amalgamates the compatible lower potentials with
the proved unrestricted theorem in arity `r ≥ 2`. It defines the upper
orientation as the intrinsic coboundary of the resulting lower potential.
`IsPotential.preserves` then gives preservation of both original upper
orientations on arbitrary vertex injections. This step uses the raw tuple
equation and has no additional order or canonical-normalization premise.

`even_strong_span` chooses finite potentials on the two sides. Their
restrictions to the base are potentials of the same upper orientation,
because both original injections preserve the base. Relative gauge
alignment changes the potential on one side while retaining that side's
upper orientation; the expanded amalgamation theorem then applies.
Evenness of the resulting upper orientation follows from `δ² = 0`.

Only the side carriers require `Finite` instances in the unordered span
theorems. Finiteness of the base follows from either input injection; no
inhabitedness or positive carrier-cardinality condition is introduced.
Potential existence and relative alignment explicitly cover the empty
base. Small carriers with no tuples of the relevant arity are also
included by the same quantified statements.

The witnesses use the literal carrier
`FiniteStrongSpan.Carrier f g = B ⊕ {c : C // c ∉ Set.range g}` and its
fixed injections `left` and `right`. Hence the exported span results have
the strong-overlap properties already proved for those maps:

```
left f g (f a) = right f g (g a)
left f g b = right f g c ↔ ∃ a, f a = b ∧ g a = c
(∃ b, left f g b = d) ∨ (∃ c, right f g c = d)
```

These properties come from `commutes`, `overlap`, and `covers`; they are
not additional assumptions about the witness. The carrier is finite, and
no unintended identifications outside the base are possible.

`potential_ordered_strong_span` and `even_ordered_strong_span` put a free
linear order on this same carrier using the proved order-shuffle theorem.
The order extends both compatible side orders on the very same vertex
maps used by the orientation amalgam. These statements impose only the
necessary order-embedding condition on an ordered input span. They do not
restrict the independent unordered results to increasing injections.

## Switching palette and the original AP interface

`Hyper.admissible_switching_iff_isEven` identifies the exact shared local
palette with vanishing of the raw tuple coboundary for every odd arity.
The normalization contributes `centralIndex n` modulo two, so this bridge
does not accidentally restrict the result to `n ≡ 3 mod 4`.

`switching_strong_span` applies this bridge to both input sides and the
result of even amalgamation. `switching_hasAP` then has exactly the existing
negative-classification interface:

```
switching_hasAP (n : ℕ) (hn : Odd n) (hn3 : 3 ≤ n) :
  HasAP n (switchingAllowed n)
```

It quantifies over arbitrary finite-ordinal input carriers and arbitrary
orientation-preserving input injections. Its witness is admissible,
preserves both sides, and commutes over the base. The final reindexing to
`Fin d` uses an actual equivalence and its inverse, so preservation and
commutation survive unchanged. Ignoring the input proof of base
admissibility is legitimate: side admissibility and an embedding already
imply the inherited base condition. The ordinary AP result is obtained
from an actual stronger exact-overlap construction.

## Verification and reviewed snapshots

An independent targeted build of the three reviewed modules completed
successfully. An additional standalone Lean check imported
`Hypertournaments.EvenAmalgamation`, inspected all eight principal exports,
instantiated `even_strong_span` at upper arity three, and checked the exact
`HasAP` wrapper type. Every selected `#print axioms` reported exactly
`propext`, `Classical.choice`, and `Quot.sound`:

- `IsPotential.intrinsic_gauge`, `IsPotential.exists_aligned`;
- `potential_strong_span`, `potential_ordered_strong_span`;
- `even_strong_span`, `even_ordered_strong_span`;
- `switching_strong_span`, `switching_hasAP`.

Reproduction commands use the unchanged receiving Lean 4.34.1 toolchain:

```
lake build Hypertournaments.EvenPotentialGauge \
  Hypertournaments.PotentialAmalgamation Hypertournaments.EvenAmalgamation
lake env lean ../preparation/EvenAmalgamationReviewCheck.lean
```

Local evidence is in
`../preparation/evidence/even-amalgamation-independent-build.log` and
`../preparation/evidence/even-amalgamation-independent-review.log`.
The frozen source snapshots reviewed have these SHA-256 hashes:

| Module | SHA-256 |
| --- | --- |
| `EvenPotentialGauge.lean` | `7b19bcdae6720de2d832a129a1ac720a9585763f773864cadcbae1fd178e039a` |
| `PotentialAmalgamation.lean` | `399d34a80906d33723f1985a4b6366f74f1e27e571a0cf46b0f2184c9a940260` |
| `EvenAmalgamation.lean` | `d0e0cb0cbc3890918d9110be8db06bb62b52b3ee41268a4bb8f298cedb1f647a` |

This review establishes the gauge and amalgamation components. Ramsey and
expansion-property arguments require their separate proofs; neither is
inferred here from amalgamation alone. No five-constrained ternary
classification is part of this work.
