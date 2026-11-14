# Affine data, free fiber codes, and actual expanded Ramsey witnesses

Source: article commit `919349e7eceed3c7fa0ed126a337c6fae6624704`, final
subsection "Further potential constructions". This package implements
the data/encoding/native-Ramsey part and the full expansion property.
Existence of potentials, gauge alignment, and strong amalgamation are
separate packages using these interfaces.

## Frozen implementation

| Module | SHA256 |
| --- | --- |
| `Affine/Data.lean` | `f460da01b42f8431f78fcddca3ce65741db6842f2d79804fc175ae1903e1d2db` |
| `Affine/FiberCoding.lean` | `dd8ec2ba47516a7437f23e3bc9edb344cf0ea257f5c169184ec3094d42c399da` |
| `Affine/ExpansionLanguage.lean` | `5bad741d8badd22c6e07821f3760682e601c3fed7abcd1ca8147eb8c570835b8` |
| `Affine/ExpansionCoding.lean` | `c9ffe477729a7f3d3e99ca706ce64fb378197bb9691672001a9fef3c05dc7008` |
| `Affine/ExpansionRamsey.lean` | `d397ddeccf8ac8da4cf3d901dbea5a1d63129764214f6b0a80d32b1a7c79aaa6` |
| `Affine/ExpansionProperty.lean` | `908b4cb9a5b17f2d610654541bd994b997baf440fae0e2420f6fe38dd9b8c58e` |

The paths in this table are under `Hypertournaments/`.

`Data Q G` contains the involutive palette, affine offset, surjective
effective map, and its equivariance equation. `Closed` and `IsPotential`
use the actual signed coboundary on injective tuples. `Expansion r d V`
names the raw structure of arity `r+1`, one affine potential of arity
`r`, and its actual compatibility equation. These definitions have no
finiteness hypotheses. The `Expansion.finite` instance proves finiteness
on a fixed finite carrier when both palettes are finite.

## Why the code palette is free

The code palette is `Q × Bool`, with the involution flipping the Boolean
coordinate. For every effective value `g`, `fiberLabel g` parametrizes
the whole effective fiber using `Q`; elements outside the fiber are
replaced by one chosen element of that fiber. The decoder reads a false
code by `fiberLabel g`, and a true code by applying the original palette
involution to `fiberLabel (offset-g)`.

`decode_effective`, `decode_star`, and `decode_section` prove the exact
fiber condition, equivariance, and a section on every fiber. No
fixed-point-free assumption is imposed on the original palette, and
decoding is allowed to identify distinct codes. The free Boolean sheet
is essential: the code follows the tuple's orientation even at fixed
original labels.

`decodeLabelled` is intrinsic and does not mention a linear order.
`encode` chooses false codes on increasing source tuples, then applies
the free permutation law to all tuples. `decode_encode` reconstructs
the actual raw structure everywhere. `encode_preserves` handles the
original increasing source embeddings. `decode_fixed_code` proves that
one fixed intrinsic code decodes to the same raw structure for every
potential of that raw structure; it has no vertex-order parameter.
This is the interface needed after changing a potential or a free
order. Source re-encoding is not needed for that step.

## Native Ramsey transport

The expansion language reuses the exact native pair language, naming
every raw and potential label and adding a free strict order. Its
embeddings preserve and reflect both label relations on every tuple,
including repeated coordinates. Class membership requires finiteness
of the entire carrier and an actual compatible expansion.

`Data.decodePair` decodes independent potential/free-code structures
into an actual expansion. It uses the proved signed-coboundary palette
law under the source's condition `Even (r+1) -> offset=0`.
`Expansion.toCodePair` gives the initial source encoding, and
`Expansion.decode_toCodePair` recovers the original actual expansion.
Both full native embedding transport maps retain the original vertex
function. The Ramsey proof obtains an actual finite independent-pair
witness from the pinned native Ramsey theorem, decodes its entire
carrier, and transports the original coloring. Composition equality is
proved pointwise. The result is the original native `Structure.Arrow`,
not a completion predicate or a conditional provider.

Public endpoints are `exists_expansion_ordered_ramsey_witness` and
`expansion_ordered_ramsey`. They retain arbitrary carrier and color
universes, finite source/middle carriers, and finite nonempty colors.
No finiteness of `Q` or `G` is needed for these Ramsey arrows; the finite
palette assumptions enter the separate precompactness assertion.

## Verification

`lake build Hypertournaments.Affine.ExpansionRamsey` passed, 1234 jobs,
with no warnings from these five modules. A full defining-module audit
checked all 96 public, private, and generated declarations against
`propext`, `Classical.choice`, and `Quot.sound`; all passed.

`../preparation/AffineExpansionChecks.lean` and its adjacent log record:

- actual fixed original labels and distinct free codes decoding to the
  same label (`Bool` with the trivial involution and effective group
  `ZMod 1`);
- an actual expanded native Ramsey arrow with an empty source in
  `Type 1`, a one-point middle carrier in `Type 1`, target `Type 1`, and
  a nonempty finite color type in `Type 1`;
- reconstruction with the same old-order source code after an
  arbitrary potential change, with an unrelated new order in scope.

The build log is `../preparation/affine-expansion-build.log`. The
complete defining-module audit is included in
`../preparation/affine-expansion-checks.log`.

## Full expansion property

`Affine.expansion_property r hr d ha rawA hA` assumes `2 <= r`, finite
palettes `Q` and `G`, a finite source carrier, the source's affine
parity condition, and actual closedness of the source raw structure.
It chooses one finite closed raw target before quantifying over all
source and target potentials and all free linear orders. Its conclusion
is an actual embedding in the original expanded native language.

The construction first chooses a finite pair host containing every
independent potential/code pair on the fixed source carrier, with
every source order. A small anchor on `ULift (Fin (r-1))` supplies a
real reference copy for the lower-gauge Ramsey coloring. Its two label
structures have no tuples, so each increasing lower tuple is a full
native copy of that anchor. The pair Ramsey theorem and pair ordering
property then fix one finite target `(p0, code)` before any new target
potential or order is chosen. Decoding supplies its closed raw reduct.

A new target potential differs from `p0` by a proved signed lower
gauge. A homogeneous copy has signed drift zero when `r` is even and
one constant `b` when `r` is odd. The all-model host contains the source
pair whose lower labels have been shifted by the opposite drift and
whose original oriented code is retained. The proof checks potential
preservation on canonical increasing tuples, cancels the two shifts,
and recovers all enumerations by the actual affine permutation law.
No assertion that this auxiliary shifted pair is itself a compatible
potential expansion is required: its host accepts independent pairs.

The final map preserves the source's original potential and its
original code. The fixed-code decoder proves that the same target code
reconstructs the same raw target for the arbitrarily chosen new target
potential. The full native embedding lift therefore returns an
embedding of the original expansions, preserving and reflecting both
actual label structures and the chosen orders. At no step are new
orders used to re-encode the fixed target code; injectivity of decoding
or uniqueness of codes is not assumed.

The EP module built with 1259 jobs and no own warnings. Its complete
defining-module audit checked all 16 declarations, including private
and generated declarations, against the standard three-axiom allowlist.
`../preparation/AffineExpansionPropertyChecks.lean` preserves the full
EP quantifier order in two kernel-checked specializations: `r=2` with
nonzero offset `1` over `ZMod 3` and an empty source in `Type 1`, and
`r=3` with offset zero over `ZMod 3` on `Fin 4`. These exercise both
arity parities without a characteristic-two assumption. Logs are
`../preparation/affine-ep-build.log` and `affine-ep-checks.log`.

Final import-only cleanup added direct `Mathlib.Tactic.Ext` to Data and
`Mathlib.Tactic.SplitIfs` to FiberCoding. Both Ramsey and EP targets
rebuilt successfully, 1260 jobs; the source hashes above include these
imports. No mathematical declaration changed. The final build log is
`../preparation/affine-final-import-build.log`.
