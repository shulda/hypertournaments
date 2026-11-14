# Local EPPA obstructions, class consequences and arity transfer

## Source and scope

Source: `shulda/tex_hypertournaments` at
`919349e7eceed3c7fa0ed126a337c6fae6624704`,
`prop:higharity-eppa-obstruction`, `thm:higharity-no-eppa`,
`prop:even-eppa-transfer` and `cor:even-no-eppa`.
The proof preparation spells out the elementary group argument used by the
preceding work package. This package extends main
`4759c8f405fc657450e1ac286eaa16957ecc4be6`.

All statements retain the original intrinsic `Hyper`, `Preserves`, ordinary
`HasEPPA` and finite-witness definitions. No coherent extension property is
assumed. The Lean/Mathlib pins and immutable Ramsey provider closure are retained.

## Local action and honest lifting

`EPPAExtension` constructs the literal induced partial automorphism between
the ranges of any two preserving embeddings of the same structure. An ordinary
EPPA witness therefore extends that isomorphism on every original vertex.

`LocalKleinAutomorphisms` uses Mathlib's standard Klein subgroup of the
alternating group on four letters. Its even permutations are extended by
identity along the four selected base vertices. The exact normalized-packet
permutation law and equality of the four colors prove preservation of the
**whole** packet, including the distinguished last vertex. The local action
is faithful, fixes that last vertex and fixes all other base vertices.

`EPPAKleinLift` forms the subgroup of pairs of an ambient automorphism and
a local Klein element whose actions agree on the embedded packet. Projection
onto the Klein group is surjective by ordinary separate EPPA extensions.
Its kernel embeds by an actual injective group homomorphism into the odd
pointwise stabilizer of the packet. The proved Sylow restriction equivalence
then supplies an actual homomorphic section and ambient Klein action.
No compatibility between initially chosen EPPA extensions is assumed.
The generic lift does not assume faithfulness; the concrete obstruction
derives it from the faithful local action and the embedded packet.

## The actual local obstruction

`local_eppa_obstruction` works on any ambient carrier containing two copies
of a packet on n+1 vertices, with n≥4. Their embeddings agree on the n-point
base, their last vertices are distinct, and four normalized base facet values
agree. It concludes that the ambient structure has no unrestricted finite
EPPA witness. It does not assume that the two copies cover the carrier.
`local_eppa_obstruction_no_witness` excludes target witnesses on arbitrary
finite carriers and in arbitrary universes.

`KleinStabilizerRigidity` uses the actual normalizer conjugation action on the
pointwise base stabilizer K. Its subgroup H stabilizing the distinguished point
is Klein-invariant. A fixed scalar element of K commutes with a nonidentity
lifted involution. If it moved the distinguished point, that involution would
fix the n-4 old vertices outside the four-point support and two distinct
outside points. The already proved fixed-(n-2)-tuple involution lemma would
make it the identity, contradicting faithfulness. Klein centralizer saturation
therefore gives H=K. An ordinary extension of the map between the two packet
copies belongs to K and moves the point, a contradiction.

Only orientations on the two packet copies are used. No orientation involving
both extra vertices is specified, so the theorem applies to every strong
self-amalgam of the packet over its base.

## General classes and fixed-size witnesses

`FiniteHyperClass` introduces finite-class predicates on the existing finite
presentations, with explicit heredity, strong amalgamation, unboundedness and
ordinary EPPA. The actual omission-class adapters are proved separately;
the general class theorem is not restricted to omission classes.

`StrongSelfAmalgam` strongly joins two copies over their n-point base and
restricts to their exact union, using heredity. The result has exactly n+2
vertices. `FourEqualPacket` selects four equal Boolean packet entries and
reorders an unused vertex to the distinguished final position. Its proof
accounts for the global complement in normalized-packet relabeling.

The public consequences are:

- Every unbounded hereditary strong-amalgamation class in arity n≥6 contains
  an n+2-vertex obstruction and fails ordinary EPPA. The only color argument
  is that at least four of seven Boolean entries agree.
- For n≥4, a hereditary strong-amalgamation class containing a packet of
  local index d≤n-3 has such an obstruction, including the next-central type.
- For each n≥4, one n+2-vertex obstruction works simultaneously for every
  pair-cancelling forbidden family, even against unrestricted finite witnesses.
  Hence every pair-cancelling omission class in these arities fails EPPA.

The common witness is constructed in the class omitting **all** finite
pair-cancelling structures. Its starting next-central packet belongs there
by the exact local PC cutoff and the PC size lower bound. These hypotheses
are proved, not provided as assumptions of the common-witness theorem.

## Even cones and link witnesses

`EvenCone` constructs a rooted even extension on `Option V` of each finite
even-arity lower structure. The root is `none`; old vertices are `some x`.
Its root link is the original orientation on every injective tuple, and its
old restriction is the intrinsic coboundary. The public construction has no
vertex-order assumption and covers r=0 and empty lower carriers.

`ConeNaturality` eliminates the construction's auxiliary finite enumeration
through the root/old characterization. Every original preserving injection
extends along `Option.map` to a preserving cone injection.

`OnePointLink` defines the actual lower orientation on the full complement
of a vertex. Every upper automorphism fixing that vertex restricts to an
automorphism of the link. `EPPASourceTransport` proves witness restriction
along original preserving embeddings and EPPA on arbitrary finite source
carriers, closing the finite-presentation transport obligation.

`evenCone_witness_link` turns any finite upper witness for the cone into a
finite lower witness. For a partial map of the lower structure, take the cone
of its domain and its two actual embeddings into the original cone. Ordinary
EPPA extends their isomorphism and explicitly fixes the root. Restrict the
result to the full link. Empty domains still contain the added root. The
upper witness itself need not be even.

## Arity-lowering and even non-EPPA

For every odd n≥3, `eppa_one_arity_down` proves that either upper EPPA
assumption (all n-hypertournaments or the even class) implies unrestricted
EPPA in arity n-1. Both source-family instances are fully discharged.
At n=3 these are implications to tournament EPPA.

Combining the transfer with the empty-PC-family obstruction in the preceding
arity proves `even_not_hasEPPA` for every odd n≥5. The explicit
`even_five_not_hasEPPA` is the introduction's highlighted case.

## Validation and next boundaries

Independent mathematical/API reviews cover the local Klein action, ordinary
lifting, full local obstruction, general class consequences, rooted cone and
the actual EPPA transfer. They are recorded in:

- `LOCAL_KLEIN_ACTION_REVIEW_2026-11-14.md`;
- `EPPA_LIFT_REVIEW_2026-11-14.md`;
- `LOCAL_EPPA_OBSTRUCTION_REVIEW_2026-11-14.md`;
- `EPPA_CONSEQUENCES_REVIEW_2026-11-14.md`;
- `EVEN_CONE_REVIEW_2026-11-14.md`;
- `EPPA_TRANSFER_REVIEW_2026-11-14.md`.

The full source/build/four-prefix axiom receipt is
`verification/high_arity_eppa_2026-11-14.json`. Exact proposed-head and
post-merge main CI evidence is recorded in the PR metadata. The only allowed
axioms are `propext`, `Classical.choice` and `Quot.sound`.

Remaining article boundaries include the finite cyclic-order encoding and
its small-arity SAP/non-EPPA consequences, and the infinite pair-cancelling
antichain/Fraisse infrastructure for continuum-many homogeneous structures.
Five-constrained ternary classification remains postponed.
