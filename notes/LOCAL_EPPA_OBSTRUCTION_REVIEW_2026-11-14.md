# Independent local EPPA obstruction review, 2026-11-14

Source: `shulda/tex_hypertournaments` at
`919349e7eceed3c7fa0ed126a337c6fae6624704`,
`prop:higharity-eppa-obstruction`, compared with the expanded proof preparation.
Reviewed frozen `KleinStabilizerRigidity.lean` and
`LocalEPPAObstruction.lean`, including their use of the actual packet action
and previously proved ordinary-extension lift. No blocking mathematical or
API issue was found. The reviewer did not change either reviewed proof file.

## Actual normalizer and centralizer argument

`klein_pointwiseStabilizer_fixes` uses the actual pointwise stabilizer K
inside the actual orientation-preserving automorphism group of B.
The hypothesis that every scalar maps the base into itself also applies to
inverse scalars. This proves that the scalar homomorphism lands in the
normalizer of K. The imported normalizer action and `compHom` give literal
conjugation, with its displayed equation verified by `rfl`.

The subgroup H is exactly the stabilizer of x inside K. It is invariant
under that conjugation action because all scalar automorphisms fix x.
An element of K fixed under a nonidentity scalar therefore commutes with
that scalar. If it moves x, its image of x is also scalar-fixed. That image
lies outside the base: an injective permutation fixing every base point
cannot take an outside point to a base point.

Writing n=m+4, the complement of the four marked base indices has exactly
m elements. The proof chooses an actual injective m-tuple from that
complement and appends x and its distinct image. This gives **m+2=n-2**
distinct fixed vertices of the scalar involution. The intrinsic involution
lemma forces that scalar automorphism to be identity. Faithfulness gives
the contradiction with its nonidentity scalar.

This argument needs only that the action's **restriction to the base** is
supported on the four marked points. Ambient points outside the base may
move. The clarified theorem comment now expresses that exact scope.

Finally K has odd order by the proved pointwise-stabilizer theorem applied
to an actual n-2 subtuple of the base. All hypotheses of the source-exact
Klein centralizer-saturation theorem are discharged; H=K gives the claimed
fixed-point conclusion. There is no unproved conjugation, normalizer,
cardinality, or generation provider.

## Local configuration and ordinary EPPA

`local_eppa_obstruction` starts with two orientation-preserving packet
embeddings f,g into the same intrinsic ambient structure A. They agree on
their n base vertices and have distinct final vertices. The four equal
normalized values belong to distinct base coordinates, supplied by the
actual injection `Fin 4 ↪ Fin n`.

The packet action is the standard Klein subgroup on four letters, embedded
by the identity outside those coordinates. Its sign is positive, so equality
of the marked normalized values gives preservation of every oriented packet
tuple through the exact facet-recovery theorem. Thus it is an actual
homomorphism to the automorphism group of the **whole packet**, not merely
of its n-vertex base. Its faithfulness and fixed-final-point properties are
the proved properties used by the obstruction.

The ordinary EPPA lift supplies an actual homomorphism to the witness's
automorphism group. Faithfulness of this lifted homomorphism is **derived**
from the literal extension equation and injectivity of the packet embedding;
it is not a premise about separate EPPA extensions. No coherence of those
extensions is assumed.

The lifted action preserves the base set because the local permutation
fixes the final packet point; it fixes each base point outside the four
marked indices. The rigidity theorem therefore applies. Separately, ordinary
EPPA extends the actual induced isomorphism from the f-copy to the g-copy.
This automorphism fixes the base pointwise but moves the final point,
contradicting rigidity.

The ambient formulation is a valid strengthening of the source: A need not
have exactly n+2 vertices, and no covering or finite-source premise is
needed. Only the two packet copies are used. No orientation involving both
new vertices is prescribed. `local_eppa_obstruction_no_witness` excludes
witnesses on any finite carrier and in any universe by the already proved
finite-target transport, so its conclusion is genuinely unrestricted.

## Validation and frozen snapshots

An independent two-target build passed (1606 jobs). Focused axiom prints
for all three public endpoints reported exactly `propext`,
`Classical.choice`, and `Quot.sound`. An additional Lean check specialized
rigidity to n=4, where the old fixed tuple has length zero, and verified
the actual normalizer-conjugation equation independently by `rfl`.

Evidence: `../preparation/local-eppa-independent-build.log` and
`../preparation/local-eppa-independent-axioms.log`.

| Module | SHA-256 |
| --- | --- |
| `KleinStabilizerRigidity.lean` | `965c8cf22d10e41b02b106566137e11293c9b71d17c14fb08528a5ee37856034` |
| `LocalEPPAObstruction.lean` | `c091baa3ad2133110b4132b6904c47980722de8eaa6468f50831e090c53b4026` |
