# Independent signed coboundary review, 2026-11-14

Source: `shulda/tex_hypertournaments` at
`919349e7eceed3c7fa0ed126a337c6fae6624704`, final subsection
`Further potential constructions`. Reviewed frozen
`Affine/SignedCoboundary.lean`, authored independently of this reviewer.
No blocking mathematical or API issue was found, and the reviewer did
not modify the reviewed proof file.

## Actual operator and integral cancellation

`signedCoboundary` is the literal sum over all deleted coordinates of
an injective tuple, with coefficient `(-1 : Int)^i.val` acting by integer
scalar multiplication. The values lie in an arbitrary additive
commutative group. There is no characteristic-two, finiteness,
linearity-of-the-input, symmetry, or alternation hypothesis.

The zero, addition, negation, and subtraction identities follow from
the actual scalar action and finite sum. Naturality uses every original
vertex injection: deleting a coordinate commutes definitionally with
composition of embeddings. No carrier order is present.

For the double coboundary, the summation indices are the actual two
successive deleted coordinates `(i,j)`. Their pairing sends them to
`(i.succAbove j, j.predAbove i)`, which deletes the same two original
vertices in the other order. The imported `succAbove` identities prove
equality of the resulting injective tuples and prove that the pairing
is an involution.

This pairing has no fixed point because its first coordinate differs
from `i`. The coefficient lemma treats both possible relative positions
of the two deleted vertices. In each case the sum of the new deletion
indices differs by one from the original sum, so the integral
coefficient is negated. The paired group values therefore add to zero
by ordinary additive inverses. The proof does not replace a negative
value by a positive one as in the earlier characteristic-two package.

The `n = 0` boundary is included: a zero-arity input has a constant
one-arity coboundary, whose next coboundary cancels with coefficients
`+1` and `-1`. Empty carriers are harmless because the conclusion still
quantifies actual injective tuples.

## Validation and frozen snapshot

An independent target build passed (1018 jobs). Six focused axiom
prints for addition, negation, subtraction, naturality, the deletion
coefficient lemma, and the double coboundary all stayed within
`propext`, `Classical.choice`, and `Quot.sound`. The coefficient lemma
uses only `propext` and `Quot.sound`.

Additional kernel-checked examples cover a zero-arity cochain with
integer value seven, a genuine signed integer edge with value one,
the double coboundary of an arbitrary non-alternating tuple function,
and a higher-universe carrier in arity zero. No reviewed declaration
contains `sorry`, `admit`, a custom axiom, `native_decide`, or `unsafe`.

Evidence: `../preparation/affine-signed-coboundary-independent-build.log`,
`../preparation/affine-signed-coboundary-independent-check.lean`, and
`../preparation/affine-signed-coboundary-independent-axioms.log`.

| Module | SHA-256 |
| --- | --- |
| `Affine/SignedCoboundary.lean` | `d62b6e1daeebcc9222dfc6d61de8dcd40cf4a9b2d3a81519b77813e78df5e9f8` |
