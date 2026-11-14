# Independent exact local pair-cancellation review, 2026-11-14

Reviewed the frozen `NormalizedPacketPermutation`, `LocalBalancedPacket`,
`LocalConstantLink`, and `LocalPairCancellationConverse` modules together
with the forward `LocalPairCancellation` module. The mathematical source
is `lem:local-types` in `shulda/tex_hypertournaments` at
`919349e7eceed3c7fa0ed126a337c6fae6624704`, with its expanded argument in
the recovered proof preparation.

No blocking mathematical or API issue was found. The final theorem is
the full intended criterion, for every intrinsic packet presentation
`A : Hyper n (Fin (n+1))` and every `n ≥ 3`:

```
PairCancelling A ↔
  localIndex A (Function.Embedding.refl _) ≤ centralIndex n - 2
```

The forward cutoff direction and its quantification over arbitrary
auxiliary orders are also reviewed in
`POSITIVE_CLASSIFICATION_REVIEW_2026-11-14.md`. The following points check
the reverse direction rather than infer it from local-index invariance.

## Global complement in packet permutation

`normalizedFacet_perm_up_to_complement` proves that an arbitrary
coordinate permutation permutes the entire normalized packet and may
complement all of its entries. The complement is one global Boolean
constant, chosen before the facet index is quantified. The statement
does not incorrectly assert that the normalized packet is simply
permuted with no parity change.

The proof uses the actual adjacent-swap normalized-facet law, and the
composition step respects the order of permutation application. Combining
two changes combines their two global complements by XOR. Determining
the complement as an explicit permutation sign is unnecessary for the
later argument: a global complement preserves alternation of a tail.

## Balanced packet and an actual full permutation

`exists_boolPacket_permutation_of_count_eq` builds a permutation matching
every target coordinate to an original coordinate of the same color.
It uses equivalences of both Boolean color classes, including the
complement class; no entries are lost or repeated.

`exists_perm_alternating_tail` then chooses two initial bits and an
alternating tail with exactly the original total positive count. Its
assumption that both original color classes have at least `k/2` entries
is sufficient for a packet of length `k+2`:

- If `k` is even, possible positive counts are `k/2`, `k/2+1`, or `k/2+2`.
- If `k` is odd, there is one further possibility, handled by an
  alternating tail starting with the other color.

The count computation supplies the correct total in all cases, and the
preceding color-class equivalence gives an actual permutation of all
`k+2` coordinates. Thus exactly two coordinates lie outside the selected
alternating tail. These are not abstract target counts without a
realization on the original packet.

## Actual auxiliary order and all pair links

`not_pairCancelling_of_constant_full_tail` requires a bijective full
tuple. This surjectivity condition is essential and is correctly supplied
by the coordinate permutation in the converse proof.

The helper constructs an auxiliary linear order on the original carrier
by transporting the standard finite-ordinal order along that full tuple.
Its distinguished pair is the first two vertices of the tuple. It then
pulls an arbitrary pair-link tuple back through the same equivalence.
The result is an increasing embedding fixing the first two indices.
Since its image omits exactly one vertex, it must be the standard facet
deleting one tail index. The proof uses equality of increasing
enumerations of the same support to establish this actual tuple
equality.

Consequently every possible pair link in this chosen auxiliary order
is one of the assumed constant raw facets. Showing constancy of a
selected list of links alone would not suffice; the helper proves the
required exhaustion of all links. Applying the universal order-and-pair
quantifiers of `PairCancelling` to this specific order and pair now gives
the contradiction. It neither assumes the original default order on the
carrier nor changes the underlying orientation.

## The reverse implication and arity boundary

For `n=k+1 ≥ 3`, failure of the cutoff gives local minority count at
least `k/2 = centralIndex n - 1`. The balanced-packet lemma arranges an
alternating normalized tail. The actual normalized tail after applying
the permutation may additionally have the global complement described
above. That complement is absorbed into its initial Boolean value.

Passing from normalized facets to raw facets cancels the alternating
coordinate parity, since indices `i` and `i+2` have equal parity. The
result is one constant raw orientation on all tail-deleted facets, so
the auxiliary-order helper proves failure of pair cancellation.
There is no parity restriction on the chosen permutation, no unproved
order-invariance of raw orientations, and no per-coordinate choice of
the global complement.

The final equivalence retains `3 ≤ n`. This ensures the distinguished
pair and all needed indices exist and `centralIndex n ≥ 2`, avoiding
any incorrect conclusion from truncated natural subtraction. It covers
`n=3`, where pair cancellation is equivalent to local index zero.
Together with the existing bound `localIndex ≤ centralIndex`, it also
implies that precisely the two central indices fail pair cancellation.

## Independent checks and frozen snapshots

An independent build of `Hypertournaments.LocalPairCancellationConverse`
passed with 1518 jobs. A separate Lean check inspected six principal
exports and verified both the `n=3` specialization and the exact
description of non-pair-cancelling packets as the two central indices.
All six selected axiom checks reported exactly `propext`,
`Classical.choice`, and `Quot.sound`. There are no proof placeholders,
native proof shortcuts, classification-provider premises, or completion
assumptions in these local results.

Reproduction commands:

```
lake build Hypertournaments.LocalPairCancellationConverse
lake env lean ../preparation/LocalPairCancellationReviewCheck.lean
```

Local evidence is in
`../preparation/evidence/local-pair-cancellation-independent-build.log`
and `../preparation/evidence/local-pair-cancellation-independent-exports.log`.

| Module | SHA-256 |
| --- | --- |
| `LocalPairCancellation.lean` | `403a75f600a03e2a1f847b00ebeea32950abd35b06b1e63e5fa95794fc2d68fc` |
| `NormalizedPacketPermutation.lean` | `8db19f088d2a4d53f0d5a449b0ac43216a77d697e02e1b0f498026dcb1fb3d44` |
| `LocalBalancedPacket.lean` | `76203b1724b8917b649ae5ef279a28741183abc35b310d839cbde6cfc97ae294` |
| `LocalConstantLink.lean` | `4caa46bee2f60972923edf275802cdcd6bd2b0765994102cfb4d11ecd6c6e0f0` |
| `LocalPairCancellationConverse.lean` | `8cad9279a478f661e237731e19b9a1dfc3b8fa358249056adf69549cd2ce78ce` |

No proof files were changed during this independent review. This is the
local `(n+1)`-vertex criterion, not the postponed five-constrained ternary
classification.
