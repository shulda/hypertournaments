# Independent review: affine constant shifts, homogeneous gauges, and the even specialization

Reviewed on 2026-11-14 against article source commit
`919349e7eceed3c7fa0ed126a337c6fae6624704`, the final subsection
"Further potential constructions", and the original even-potential
construction earlier in the same source. The reviewer did not edit any
of the three reviewed implementation files.

## Final source hashes

| Module under `Hypertournaments/Affine/` | SHA256 |
| --- | --- |
| `ConstantShift.lean` | `57fcd90bcd52c6967016fb59fbd8213ad6482f575419c528946bee9f1976ddf2` |
| `HomogeneousGauge.lean` | `64d2cdad06bb842bebb3020d2f0b163dd4b5d424ef4245e2ec01786b0a835907` |
| `EvenSpecialization.lean` | `79bc163f878fb77785e9d9a1b4e9f5a38678da94024f642eaaaf8782ddcf3061` |

## Constant shifts and the arity convention

Constants mean constant labels on increasing tuples, extended by the
ordinary negation permutation law to every enumeration. They are not
asserted to have the same group value on all ordered tuples. The signed
sum of `m` equal facets is zero for even `m` and the common value for
odd `m`; the implementation proves this over an arbitrary additive
commutative group.

| Input ordinary cochain arity | Coboundary arity | Value on increasing upper tuples |
| --- | --- | --- |
| even `r` | odd `r+1` | `b` |
| odd `r` | even `r+1` | `0` |

`constantLinear_coboundary` is an equality of actual alternating label
structures, proved from canonical increasing tuples and the full
permutation law. Consequently the odd-degree closedness and
potential-shift conclusions hold on every injective tuple. The affine
shift adds an ordinary alternating cochain, so it retains the original
affine offset. No characteristic-two, two-divisibility, finite-palette,
finite-carrier, or inhabited-carrier assumption is used.

## Homogeneous lower gauges

The homogeneous gauge has arity `n`; its coboundary has arity `n+1`.
The latter is the potential arity in the expansion-property argument.
The resulting drift is therefore zero for even potential arity and
`b` for odd potential arity. This agrees with the constant-shift table
above and does not confuse potential arity with raw-structure arity.

Homogeneity is assumed exactly on increasing lower tuples of the
ordered source. Each facet of an increasing upper tuple is increasing,
which supplies all equal facet values. `homogeneous_coboundary_pullback`
then recovers an equality of actual ordinary alternating structures,
not merely equality on canonical tuples. Its target carrier has no
order assumption; its given vertex injection need not be increasing
for any target order.

Both gauge directions were checked. For
`q(e t) = p(t) + Delta s(e t)`, the source shift is the positive drift.
For `p(t) = q(e t) + Delta s(e t)`, the source shift is the negative
drift. Both conclusions use the actual original injection and preserve
every tuple label. Small and empty carriers are included: if upper
tuples do not exist, the canonical checks are correctly vacuous; no
extra embedding or nonempty subset is assumed by these helper lemmas.

## The original even construction is recovered exactly

`evenData` uses the original Boolean raw orientation palette, the group
`ZMod 2`, offset `1`, and the original bit map `false -> 0`, `true -> 1`.
Its palette law is exactly `eta(!b) = 1-eta(b)`, and its effective map
is proved surjective. Both Boolean/group round trips are provided.
Every integral sign acts trivially in `ZMod 2`, so the signed operator
is proved equal to the original unsigned tuple coboundary, with the
same literal deleted-face tuples.

The two explicit equivalences on an unchanged carrier identify:

- original hypertournaments with Boolean-labelled structures;
- original hypertournaments with group-labelled structures having
  affine involution `g -> 1-g`.

Both inverses are actual label constructions. In particular the group
inverse includes every new group-labelled potential, not only ones
introduced by a preceding original-to-new conversion. The forward and
inverse coboundary theorems are equalities of actual original/new
structures. The four preservation equivalences retain the original
arbitrary vertex embeddings and exact label equality.

`Closed evenData A.toAffine <-> A.IsEven` and both specified-potential
bridges use the same original tuple equations. These predicate
identities themselves have no arity or finiteness restriction.
Constructing the actual next-arity coboundary, and deriving the old
finite potential-existence theorem, correctly require **even lower
potential arity `r`**, hence odd raw arity `r+1`. This supplies the
general affine offset condition: an even raw arity would require the
offset to be zero, whereas this specialization has offset one.
There is no extension of the offset-one constructor to the forbidden
opposite parity.

`Hyper.isEven_iff_exists_potential_via_affine` derives the old finite
existence statement from the new `closed_iff_exists_potential` and the
two-sided bridge. Its body does not call the earlier original
potential-existence theorem. The only finite-carrier hypothesis enters
at the general affine existence theorem. The bridge does not reindex
the source carrier or introduce an auxiliary order into the conclusion.

## Independent verification

- Independent build of all three targets passed, 1645 jobs. The three
  reviewed modules emitted no warnings; existing dependency warnings
  were replayed. This build was repeated after the final unrelated
  direct-import cleanup in Data and FiberCoding.
- A defining-module audit checked all 55 declarations attributed to
  these three modules, including generated and private declarations.
  Every transitive axiom dependency was in
  `propext`, `Classical.choice`, `Quot.sound`; `boolPalette` uses none.
- Independent integral tests checked constant degree two on `Fin 3`
  gives `5` on the increasing triple and `-5` on a transposed triple,
  while degree three gives zero on **every** four-tuple. Thus the tests
  distinguish ordinary alternation from a characteristic-two shortcut.
- Additional kernel checks exercised the ternary closedness bridge on
  arbitrary carriers in `Type 1`, the arbitrary-new-potential bridge in
  raw arity five, inverse actual coboundaries in lower arity two, and
  existence of original arity-four potentials via the new theorem.
- A separate example recovered an original arity-two potential for
  every ternary hypertournament on `ULift.{1} (Fin 0)`, using vacuous
  closedness and the new affine existence theorem. This checks the
  empty-carrier and nonzero-universe boundary.

Reproducible evidence is in
`../preparation/AffineSpecializationReviewCheck.lean`,
`affine-specialization-review-checks.log`, and
`affine-specialization-review-build.log`.

No mathematical, parity, carrier, or interface defect was found.

## Final direct-import confirmation

The final ConstantShift source adds only a direct
`Mathlib.Tactic.SplitIfs` import. Independent byte-level verification
removed precisely that import line and reproduced the previously
reviewed source SHA256; thus no declaration, proof, or hypothesis
changed. The table above records the new final hash. The other two
reviewed module hashes are unchanged. An independent rebuild of
`Hypertournaments.Affine.ConstantShift` passed, 1117 jobs, with no own
warnings; its log is
`../preparation/affine-specialization-review-final-import.log`. The
author's corresponding import-cleanup build is recorded in
`../preparation/affine-final-splitifs-import-build.log`.
