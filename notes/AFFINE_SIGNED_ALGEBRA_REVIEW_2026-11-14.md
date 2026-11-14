# Independent review of the signed affine algebra

Reviewed on 2026-11-14 against article commit
`919349e7eceed3c7fa0ed126a337c6fae6624704`, subsection
“Further potential constructions”. The reviewed files are
`Affine/SignedCoboundary.lean`, `SignedPermutation.lean`,
`SignedContraction.lean`, `SignedExactness.lean`, and
`GaugeAlignment.lean` under `Hypertournaments/`.

The reviewer authored none of these five implementations and made no proof
edits. No mathematical or interface defect was found. The authors added
the direct tactic imports required by `AGENTS.md`:
`Mathlib.Tactic.Ext` in `GaugeAlignment.lean` and
`Mathlib.Tactic.SplitIfs` in `SignedPermutation.lean`, without proof changes.
For the final SplitIfs cleanup, removing exactly that one import line
reproduced the previously reviewed file's SHA-256; all other four reviewed
file hashes were unchanged. The independent build and all five defining-module
audits were rerun on the final snapshot below.

## Signed differential and its square

`signedCoboundary` is literally

\[
  (\Delta\varphi)(f)=\sum_i(-1)^i\varphi(\operatorname{facet}(f,i)),
\]

with integer scalar multiplication in an arbitrary `AddCommGroup`. The
input may be any function on injective tuples; alternation is not assumed
for additivity, subtraction, naturality, or the square-zero theorem.
Deletion commutes definitionally with arbitrary vertex injections.

The square-zero proof pairs the two orders of deleting distinct original
coordinates. Its map on deletion indices is a fixed-point-free involution;
the two resulting ordered tuples are equal, and
`signed_deletion_coefficient` proves that their integer coefficients are
negatives. Cancellation uses additive inverses, with no division by two,
torsion restriction, or characteristic-two premise. The argument includes
initial tuple arity zero. If the carrier has too few vertices for a tested
tuple, the universal statement is simply vacuous.

## The affine offset and actual permutations

For a lower structure whose odd-coordinate involution is `g ↦ a - g`,
`signedCoboundary_adjacent` proves the unrestricted formula

\[
  \Delta p(\tau f)=
  \begin{cases}0,&r+1\text{ even},\\a,&r+1\text{ odd}\end{cases}
  -\Delta p(f)
\]

for an adjacent coordinate swap in upper arity `r + 1`. The two deleted
swapped coordinates are handled by exact facet equalities. On all other
facets the lower affine swap law applies; the surviving offset is the
actual alternating sum of the coefficients.

The same-offset theorem and `Labelled.coboundary` explicitly require
`ha : Even (r + 1) → a = 0`. This is exactly the source restriction on
the upper arity and offset. It is not replaced by a characteristic-two
assumption or imposed when the upper arity is odd. Adjacent transpositions
generate the entire permutation group, so
`signedCoboundary_label_perm` covers all ordered injective tuples and
arbitrary coordinate permutations. The constructor's swap law, its
pullback equality, and its preservation theorem retain the original
vertex injections; no ambient vertex order occurs.

## Root contraction and positive-degree exactness

`contractTuple a c` prepends the literal root when it is absent and returns
zero when it is already present. For ordinary alternating cochains this
construction has the ordinary negation involution: a coordinate swap of
the contracted tuple lifts to a swap of the successor coordinates while
fixing the prepended root.

The root-absent cone identity has its integral sign:

\[
  \Delta c(a,f)=c(f)-\Delta(h_a c)(f).
\]

In particular, the minus sign on the contracted coboundary is retained.
For a root-first tuple, only the facet deleting the root contributes to
the contracted coboundary. If the root occurs elsewhere, the proof moves
it to the first coordinate and transports both sides by their ordinary
negative swap laws. This checks every tuple, including those containing
the root, rather than only tuples avoiding it.

`exists_signed_potential` proves exactness for an ordinary alternating
cochain of arity `n + 1`, for every `n : ℕ`. On an inhabited carrier it
uses the root contraction. On an empty carrier it constructs the zero
lower cochain, and the required positive-arity tuple equations are
vacuous. Thus there is no global `Nonempty`, finite-carrier, order,
finite-group, or characteristic hypothesis. This statement concerns
ordinary alternating cochains; the construction of potentials for
general affine effective labels is a separate module and is not claimed
to have been reviewed here.

## Signed gauges and arbitrary-image extension

Subtracting two cochains with the same affine offset cancels that offset,
so `p.affineSub q` is an ordinary alternating cochain. Equality of their
signed coboundaries makes this difference closed. The exactness theorem
then gives `exists_signed_gauge` with the literal equation

\[
  p=q+\Delta s,
\]

where the lower `s` has involution `g ↦ -g`. It is a genuinely signed
cochain, not a symmetric substitute except when the coefficient group
itself makes negation trivial.

`tuplePreimage` reconstructs an injective tuple from actual containment of
all its coordinates in the image of the given injection. The choice of
preimages is cancelled using injectivity, including after coordinate
swaps. `Labelled.extendLinear` uses this preimage on wholly contained
tuples and zero on tuples with a coordinate outside the image. Its swap
law is proved in both cases, and the extension agrees with the original
cochain on every actual source tuple. Consequently its coboundary also
agrees on every source tuple. No order-preservation, surjectivity,
finiteness, or nonempty-base premise is introduced.

The arity-zero boundary is consistent: the unique empty tuple is wholly
contained in every vertex image, even an empty image, so its value is
transported rather than reset to zero. This is the correct extension of
a zero-arity cochain and is used safely by the arity-one potential case.

Adding the coboundary of the extended ordinary gauge retains the raw
potential equation by the signed square-zero identity. The relative
alignment theorem applies to a prescribed potential on an induced base
and returns an ambient potential preserving that exact base potential
along the original arbitrary injection. Its final interface has the
explicit and appropriate `0 < r` potential-arity hypothesis; the source
assumes the stronger upper-arity bound `n ≥ 3`. Empty bases and empty
ambient carriers remain included.

## Independent verification

With Lean 4.34.1 and the committed Lake manifest, the final snapshot
passed:

```
lake build Hypertournaments.Affine.GaugeAlignment
```

This target covers all five reviewed modules. The independent build
passed **1122 jobs**, with no warnings from the reviewed files; existing
dependency warnings were replayed. The log is
`../preparation/affine-signed-algebra-independent-build.log`.

The existing `axiom-audit` executable was run separately for each defining
module, importing `Hypertournaments.Affine.GaugeAlignment`, with allowlist
`propext,Classical.choice,Quot.sound`. The audit selects declarations by
their defining module, so private helpers and generated declarations are
included:

| Defining module | Audited declarations | Result |
| --- | ---: | --- |
| `SignedCoboundary` | 13 | Passed |
| `SignedPermutation` | 14 | Passed |
| `SignedContraction` | 14 | Passed |
| `SignedExactness` | 7 | Passed |
| `GaugeAlignment` | 14 | Passed |

All **62 declarations** passed, with no violations and no axioms outside
the allowlist. The JSON evidence is in
`../preparation/affine-signed-review-<Module>.json`.

Fifteen selected public definitions and theorems were also checked with
`#print axioms`; all use only the same allowlist. The deletion-coefficient
lemma uses the smaller set `[propext, Quot.sound]`. The accompanying
kernel-checked specializations cover:

* signed square-zero over `ℤ` starting at arity zero;
* positive-degree exactness on an empty carrier;
* exactness with both carrier and coefficient group equal to infinite `ℤ`;
* the actual nonzero offset `a = 1 : ℤ` in odd upper arity three;
* extension of a nonzero zero-arity cochain from an empty carrier;
* coboundary naturality for extension along the order-reversing injection
  `x ↦ -x` on `ℤ`.

All checks passed. Their output is
`../preparation/affine-signed-algebra-independent-axioms.log`. Facade
coverage, complete proposed-commit auditing, and CI remain package-level
integration checks.

## Final reviewed SHA-256

| File under `Hypertournaments/Affine/` | SHA-256 |
| --- | --- |
| `SignedCoboundary.lean` | `d62b6e1daeebcc9222dfc6d61de8dcd40cf4a9b2d3a81519b77813e78df5e9f8` |
| `SignedPermutation.lean` | `e146f52a744a885a797de0237aae996c87b3ee6dc7f7c70cd71827f7055ce1ec` |
| `SignedContraction.lean` | `1d4c44bd82d4ba9bbc0bd76fc7d51a9a73a4013f0f1ec0ceb93e12a8fe761bbb` |
| `SignedExactness.lean` | `317306f716630f8f776356ed44af0534bc32434decc8d36c15c93b3a233fd1e3` |
| `GaugeAlignment.lean` | `9ac8739606b2d44a34228c70417620a4086dcbb064970ed922159381cef886c3` |
