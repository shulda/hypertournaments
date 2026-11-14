# Independent automorphism and odd stabilizer review, 2026-11-14

Reviewed without modifying proof sources. No mathematical or interface issue
was found.

## Frozen sources and reference

The working tree is based on repository commit
`25e646469f3e0b6df77ad9c884440f62c815880d`. The reviewed new sources are identified
by their complete SHA-256 digests:

| File | SHA-256 |
| --- | --- |
| `Hypertournaments/Automorphism.lean` | `34ad6f202cdb0ac2cbeb65f59a7f4cce29c017824981eb927dbf6e11ebca0f71` |
| `Hypertournaments/OddStabilizer.lean` | `a05a280f4ebf8c55da10985bd46bfc45f54b0a291180bba8fd7ec7c357cdda08` |
| `Hypertournaments/Basic.lean` | `2f2b0f73c3242e784801661550473c859fbb41307ac87e6d95b4fb7fb9efe713` |
| `Hypertournaments/TwoPadIntrinsic.lean` | `3ee36b2dbcba8c0c1d18681a0f51266ad9f666c2c743aacc99ff1725a4ef286e` |

The article reference is `shulda/tex_hypertournaments` at
`919349e7eceed3c7fa0ed126a337c6fae6624704`. The inspected proof preparation
`hypertournaments_formalization_source.tex` has SHA-256
`912490471462f538ec27611ee2f07450bc0e9dca840084bdda1e9ca55bea917c`;
its odd pointwise stabilizer statement and proof are lines 613–624.

## The actual automorphism group and action

`Hyper.automorphismGroup` is the subgroup of the actual vertex permutation
group whose elements preserve every intrinsic injective orientation tuple.
It does not introduce an order, an auxiliary representation, or an abstract
group with an unproved action.

Permutation multiplication has the convention `(g*h)(x) = g(h(x))`.
The closure proof applies preservation by `g` to `t.trans h.toEmbedding`,
and then preservation by `h` to `t`. Thus its leftmost orientation is
precisely the image under `g*h`. The inverse proof cancels `g` after
`g.symm`, with the tuple equality checked coordinate by coordinate.
The inherited action is evaluation of these same permutations.

The exported extensionality lemma identifies automorphisms when they agree
on every vertex. A separate elaboration check also inferred
`FaithfulSMul A.Aut V` from the subgroup action, and verified the displayed
multiplication convention by `rfl`. In particular, no faithfulness premise
is omitted from the later argument.

## Involutions fixing an `(n-2)`-tuple

`Hyper.Aut.eq_one_of_sq_eq_one_of_fixes_tuple` is stated as arity `k+2`
with an actual injection `Fin k ↪ V`. It needs no finiteness assumption.
If the automorphism is nonidentity, extensionality supplies a moved vertex
`x`. Its square being one gives `g(g(x)) = x`. Both `x` and `g(x)` lie
outside the fixed tuple: membership of either would make `x` fixed.

`twoPadTuple` then constructs the genuine injective tuple
`(x, g(x), s(0), ..., s(k-1))`. The proof checks its image under `g`
coordinate by coordinate and obtains exactly the swap of coordinates zero
and one. Preservation makes this swap preserve the Boolean orientation,
while `swap_flip` makes it complement that same orientation. Exhausting
the two Boolean values gives the contradiction.

The padding assumptions are proved from the moved point and the given
fixed tuple. There is no premise that two additional vertices already
exist: they are obtained only in the nonidentity branch. This matters for
small carriers, where the argument instead forces the automorphism to be
the identity.

## Cauchy and the genuine pointwise stabilizer

`Hyper.pointwiseStabilizer S` is Mathlib's fixing subgroup for the faithful
evaluation action of `A.Aut` on the actual carrier. Its membership theorem
is the literal equation `g(x)=x` for every `x` in `S`.

Finite `V` makes its whole permutation group, its automorphism subgroup,
and this fixing subgroup finite. If the stabilizer's actual cardinality
were even, `exists_prime_orderOf_dvd_card'` with prime two supplies an
element of order exactly two in that subgroup. Its square is one, and the
equation is transported through the subgroup inclusion into `A.Aut`.
Stabilizer membership supplies the fixed tuple hypothesis. The preceding
involution theorem therefore makes the automorphism one; subtype
extensionality then makes the original subgroup element one. This
contradicts its order being two.

The final wrapper obtains the injection of `Fin (n-2)` into the specified
finite set directly from the cardinality bound. It proves oddness of the
cardinality of the pointwise stabilizer itself, without replacing it by
the cardinality of an image or quotient.

## Boundary cases and verification

The wrapper explicitly requires `2 ≤ n`, matching the article. For `n=2`,
the fixed tuple has length zero, so the theorem also applies to the empty
fixed set and yields odd order of the whole automorphism group. The
involution proof still has its two padded coordinates. For an empty
carrier the automorphism group and every stabilizer are trivial, of order
one. The source does not silently require a nonempty carrier.

For larger arities and carriers too small to contain the required fixed
tuple, the cardinality premise cannot hold. The statement makes no
incorrect assertion that such hypertournaments have odd full
automorphism groups. Arities zero and one are intentionally outside the
final wrapper's scope.

The focused target build succeeded:

```text
lake build Hypertournaments.Automorphism Hypertournaments.OddStabilizer
Build completed successfully (1507 jobs).
```

Separate Lean checks accepted the faithful-action instance, the exact
permutation-composition equation, the binary empty-fixed-set specialization
on arbitrary finite carriers, and its empty-carrier specialization.
`#print axioms` for `Hyper.automorphismGroup`, the involution theorem, and
`Hyper.odd_card_pointwiseStabilizer` reported exactly `propext`,
`Classical.choice`, and `Quot.sound`. The reviewed modules contain no
`sorry`, custom axiom, or native decision procedure.

This review establishes the automorphism and odd-stabilizer foundations.
It does not claim the later local EPPA obstruction has been proved.
