# Independent finite-mask semantic review, 2026-11-14

Reviewed `Hypertournaments/FiveConstrained/Mask.lean`, written by the separate
mask implementation agent, against the original `Hyper`, `Preserves`,
`Hyper.fromOrderedSigns`, and canonical tuple recovery APIs. The reviewer wrote
Catalogue modules but did not implement or edit the reviewed Mask module.
No blocking mathematical or API issue was found.

The orientation bit of an increasing triple is read literally. `orientAt`
implements the six possible coordinate orders with exactly the corresponding
alternating sign, and the three swap identities prove the original intrinsic
`Hyper.swap_flip` law. No vertex order is added to `Preserves`.
`maskHyper_fromOrderedSigns_orient` relates the new direct evaluator to the
pre-existing canonical sign-table construction on every injective tuple.
`preserves_iff_triples` reduces arbitrary orientation-preserving injections to
increasing source triples; it requires no order preservation of that injection.

`packBits` is little-endian, with general proofs of each coordinate bit and
its actual integer bound. `pairRank` and `tripleRank` are the lexicographic
ranks used by the source's finite certificates. The executable lookup inverse
is kernel checked uniformly for all carrier sizes below ten and all valid
increasing triples, including the bound below `n.choose 3`.

The integer encoder `maskOfHyper` is defined for every finite carrier and has
the bound `2^(n.choose 3)` in every size. Its recovery theorem explicitly
assumes `n <= 9`; the review makes no larger-carrier claim. The proved lookup
inverse and bit-packing theorem recover every increasing triple, and the
existing intrinsic canonical-recovery theorem extends equality to every
injective ordered tuple. This is enough for all retained certificate unions,
whose maximum size is nine. Carriers with fewer than three vertices are
included; orientation preservation there is vacuous. The analogous
`maskOfTripleFunction` constructor recovers any prescribed Boolean function
on valid increasing triples under the same explicit size bound.

Independent endpoint smoke checks included the largest nine-vertex carrier
and the empty carrier. Six axiom prints (`maskHyper`, the ordered-sign
comparison, the preservation criterion, the lookup inverse, full intrinsic
recovery, and arbitrary-triple-function recovery) used only subsets of
`propext`, `Classical.choice`, and `Quot.sound`. The log is
`../preparation/five-mask-independent-review.log`.

Frozen SHA-256:

`46c719592a42d7208adc3b86b1e0d7f1eb27367697ebc600b2dcde4b4cd20eae`

The complete rehashed build, facade closure and complete defining-module
axiom audits remain integration checks performed by the main task.
