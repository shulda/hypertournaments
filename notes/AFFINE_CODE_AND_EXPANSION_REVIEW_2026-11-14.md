# Independent review: affine fiber codes, Ramsey transfer, and expansion property

Reviewer: root, independent of the author of the six reviewed modules.
Article: `shulda/tex_hypertournaments` at
`919349e7eceed3c7fa0ed126a337c6fae6624704`, final subsection
`Further potential constructions`.

## Reviewed source snapshots

| File | SHA-256 |
| --- | --- |
| `Affine/Data.lean` | `f460da01b42f8431f78fcddca3ce65741db6842f2d79804fc175ae1903e1d2db` |
| `Affine/FiberCoding.lean` | `dd8ec2ba47516a7437f23e3bc9edb344cf0ea257f5c169184ec3094d42c399da` |
| `Affine/ExpansionLanguage.lean` | `5bad741d8badd22c6e07821f3760682e601c3fed7abcd1ca8147eb8c570835b8` |
| `Affine/ExpansionCoding.lean` | `c9ffe477729a7f3d3e99ca706ce64fb378197bb9691672001a9fef3c05dc7008` |
| `Affine/ExpansionRamsey.lean` | `d397ddeccf8ac8da4cf3d901dbea5a1d63129764214f6b0a80d32b1a7c79aaa6` |
| `Affine/ExpansionProperty.lean` | `908b4cb9a5b17f2d610654541bd994b997baf440fae0e2420f6fe38dd9b8c58e` |

## Data, effective labels, and oriented codes

The data exactly match the source: an involutive raw palette, an abelian
effective group, an offset, and a surjective effective map satisfying
`effective (star q) = offset - effective q`. Finiteness enters the later
finite-language/expansion-property statements; the algebraic definitions
have no extra group assumptions. Potential compatibility is equality on
every injective tuple. An expansion retains both actual structures.

The uniform auxiliary palette is `Q × Bool`, with the second coordinate
reversed by the involution. For a prescribed effective value, `fiberLabel`
keeps an already-correct raw label and otherwise chooses a member of that
fiber using the actual surjectivity proof. On the false sheet, decoding
uses that fiber label. On the true sheet, it uses the opposite effective
fiber and then the original raw involution. The two sheet cases prove both
the effective-label equation and equivariance under tuple reversal.

This handles fixed raw labels and duplicate codes. The false-sheet map
`q -> (q,false)` is a section in the correct fiber; decoding is not assumed
injective. The chosen uniform bound on auxiliary colors is the finite
size of `Q`; no optimal code-size assertion is needed.

Source encoding uses its given order only to choose the increasing
representative. The complete tuple function is recovered by the free
palette involution. `decode_encode` proves recovery on all tuples by the
canonical-reconstruction theorem. Increasing raw embeddings preserve
these source codes. Decoding and its preservation theorem themselves
use no carrier order.

## Actual native Ramsey transfer

The native language names every lower potential label, every upper raw
label, and a free strict order. Native embeddings preserve and reflect
these predicates on all tuples, including repeated coordinates.

The two source expansions are encoded as independent potential/code pairs.
The existing actual Ramsey witness for those pairs is decoded to an
actual compatible expansion. Every original source-to-middle embedding
canonically lifts to an embedding between their code pairs. Embeddings
into the arbitrary pair witness decode to embeddings of the actual
expanded structures. Composition agrees pointwise, so pulling back the
coloring gives exactly the requested `Structure.Arrow`. The class theorem
packages a genuine finite target and its actual class membership.
No uninstantiated Ramsey, completion, or coding provider remains.

## Expansion property and the duplicate-code boundary

The witness is selected before both source and target potentials and
both free orders. A finite ordered host contains every independent pair
on the fixed source carrier with every order. It also contains a genuine
small anchor with fewer vertices than the lower arity.

A pair Ramsey arrow homogenizes the signed lower gauge with colors in
the finite effective group. The pair ordering property then chooses one
fixed intrinsic pair `target = (basePotential, code)`. Decoding this pair
chooses the raw reduct witness. This happens before every later quantified
potential and order.

For any later target potential, its coboundary has the same effective
labels. `decode_fixed_code` consequently reconstructs the same raw target
using the **same original code**. The proof does not recode that target
in its new order, choose a unique code from a raw label, or quantify over
new target-code lifts. Thus repeated codes and fixed raw labels do not
introduce an unstated compatibility assumption.

The signed difference between the new and base potentials is an actual
ordinary alternating lower gauge. A real embedding of the small anchor
chooses its homogeneous value. On increasing lower tuples, its coboundary
is zero in even lower arity and that common value in odd lower arity.

The source host contains all independent pairs, so the original source
potential shifted by the negative drift, with its original code retained,
embeds into the host. After the homogeneous embedding the two shifts
cancel. The proof checks this on canonical tuples and recovers preservation
on every enumeration. The high code labels are preserved by composition.
Decoding then yields an actual native embedding preserving the original
source and target potentials, raw labels, and orders.

The public theorem requires precisely lower arity at least two, the source
offset condition in even upper arity, finite palettes/effective group, and
a finite source carrier. The closed-source premise is supported by the
independently proved actual potential-existence theorem. All source
instances are discharged, including the binary lower-arity case and
empty carriers. Target, carrier, and color universes are explicit.

## Independent verification

An independent two-target build of `ExpansionRamsey` and `ExpansionProperty`
passed with 1260 jobs. Selected prints for decode equivariance, full source
recovery, fixed-code recovery, the Ramsey witness, the Ramsey class, and
the final expansion property use only `propext`, `Classical.choice`, and
`Quot.sound`. Final direct-import-only changes were reviewed and are also
covered by the complete package build/audit receipt.

No mathematical or API gap was found. In particular, the final conclusion
is in the original expanded language and has the full expansion-property
quantifier order. The package receipt binds all reviewed source bytes and
includes the complete defining-module axiom audits.
