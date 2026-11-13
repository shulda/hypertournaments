# Independent review of the potential Ramsey and expansion properties

Date: 2026-11-13.
Source: `shulda/tex_hypertournaments` at
`919349e7eceed3c7fa0ed126a337c6fae6624704`, `thm:potential`, the definition
of the expansion property, and the proof beginning with the potential-reduct
correspondence. Also compared the longer preparation proof in section 4 of
`hypertournaments_formalization_source.tex`.

Result: no blocking mathematical or statement-level issue found. This review
is independent of the implementation of the Ramsey/expansion modules. The
reviewer implemented the separate switching and amalgamation bridges, so the
present note concentrates on the full expansion language, the finite host,
the image-of-a-subset argument, and the final quantifiers.

## Actual expanded Ramsey class

`PotentialLanguage` names both the lower orientation in arity `r` and the
upper orientation in arity `r + 1`, as well as the free vertex order.
`liftPotentialEmbedding` has the full preservation-and-reflection field for
each named relation. The upper relation follows from `IsPotential.preserves`
and the existing equivalence between intrinsic preservation and relational
equivalence on arbitrary tuples. In particular, repeated-coordinate tuples
are covered; an embedding of only the lower relation is not silently returned
as an embedding of a different language.

`potentialExpansionClass` includes finiteness of the whole carrier and the
actual tuple equation `IsPotential A φ`. This equation already implies
`A.IsEven`. Conversely, the proved finite potential-existence theorem supplies
an expansion of every even reduct when the lower arity is even. Thus the
represented class is the class in the source theorem.

In `exists_potential_ramsey_witness`, an arbitrary coloring of full expansion
embeddings is evaluated on the corresponding lifted lower embeddings. The
unrestricted Ramsey witness supplies its lower orientation; taking its actual
intrinsic coboundary supplies the named upper orientation. Forgetting any two
full embeddings gives lower embeddings to which Ramsey homogeneity applies.
The explicit equality of lifted composites, proved by `Embedding.ext`, then
returns homogeneity for the original full coloring. There is no additional
class-provider or completion premise. The assumption `2 ≤ r` includes the
binary-potential/ternary-upper case through the proved unrestricted binary
Ramsey theorem.

## One host before either expansion is chosen

`exists_all_potential_order_host` enumerates all actual members of
`Hyper r V`, rather than assuming finitely many orders or enumerating only
already chosen potentials. Its finiteness proof is the injection sending a
hypertournament to its orientation function; injectivity follows from
`Hyper.ext`, and the function domain and codomain are finite.

The finite joint-embedding theorem constructs one host for all these
orientations with a single fixed canonical order. To obtain a requested order
of an arbitrary `φ`, the proof uses the permutation `σ` underlying the order
isomorphism from the canonical order to the requested order. The enumerated
model is exactly `φ.pullback σ`, and `orderExpansionReindex` maps the requested
source into it using `σ⁻¹`. The orientation verification uses `σ ∘ σ⁻¹ = id`;
no assertion that the original orientation is order-invariant is needed.
The subsequent joint-host embedding composes with this genuine reindexing
embedding. Hence the host is selected before both the orientation and order
later requested by the final theorem. Enumerating all lower orientations is
a valid stronger host construction than enumerating only potentials of `A`.

## What gauge homogeneity actually proves

The scalar gauge has degree `r - 1`, and `smallGaugeModel r` has exactly
`r - 1` vertices in a language whose orientation relation has arity `r`.
Every order embedding of this small model preserves its orientation because
there is no injective `r`-tuple on its carrier.

For an actual `r`-tuple in the homogeneous copy, the helper constructs such
a full ordered embedding separately for each of its deleted-point facets.
The support identities identify its image with the image of that facet.
The coboundary is then computed on the mapped finite support using the
proved map/erase identity. Pairwise Ramsey homogeneity makes all `r` summands
equal to some scalar `b`, and evenness of `r` proves `r • b = 0` in `ZMod 2`.

The proof requires only that the **coboundary** of the gauge vanish on those
image supports. It never assumes the gauge itself is zero, or globally
constant. The common scalar `b` may be nonzero. A baseline small embedding
is constructed from a facet whenever an `r`-tuple is being considered, so the
argument also handles carriers with no such tuples. An external nonempty
carrier or a separate global baseline is not required.

`gauge_homogeneity_preserves` combines this cancellation with the actual
intrinsic gauge equation on every ordered tuple and the existing preservation
of the original potential. It proves preservation of the switched potential
by the same vertex injection, rather than replacing the copy by a new map.

## Full expansion-property quantifiers

`potential_expansion_property` first selects its host `D`, Ramsey witness `C`,
ordering-property witness `(W, φ₀)`, and upper reduct
`B = φ₀.coboundary hr`. It proves `B.IsEven` and only then introduces all four
choices: the source potential and order, and the target potential and order.
Thus `B` is independent of either expansion, exactly as required by the
source definition. The final potential equations are premises concerning
these universally quantified choices, not assumptions used to choose `B`.

For a target potential `ψ`, `hψ.intrinsic_gauge` is used in the correct
direction: `bit ψ = bit φ₀ + δz`. The ordering property supplies
`f : C → (W, φ₀, orderB)`. The Ramsey coloring is the scalar gauge evaluated
on the image of a small-model embedding followed by `f`; the homogeneous
map `g : D → C` gives `h = f.comp g`. The helper shows this same `h`
preserves `ψ`. Its original strict monotonicity still concerns precisely the
requested `orderB`, so the resulting map preserves both `ψ` and that order.
Composing with the all-potential host embedding gives the requested ordered
source potential map, and `liftPotentialEmbedding hφ hψ` recovers the full
embedding preserving and reflecting both named orientations.

The source-evenness premise is retained in the public theorem. Its proof
does not use it to choose the host because the host includes all lower
orientations; the supplied source potential equation already forces source
evenness when the embedding assertion is invoked. This is harmless and
introduces no stronger hypothesis. Empty source carriers are included. The
positive lower-arity assumption supplies the exact range in which the
empty-carrier gauge theorem is valid. The binary ordering input, including
its two-edge-type argument, was reviewed separately in
`ORDERING_POTENTIAL_REVIEW_2026-11-13.md`.

## Checked versions and verification

The implementation agent's target build of `PotentialExpansionProperty`
completed successfully (1783 jobs). An independent readable axiom check of
the full class Ramsey theorem, the universal host, both gauge-homogeneity
helpers, and the final expansion theorem reported exactly `propext`,
`Classical.choice`, and `Quot.sound`. The complete proposed-commit build and
whole-project audit remain the integrator's checks.

SHA-256 hashes of the reviewed sources:

| Module | SHA-256 |
| --- | --- |
| `PotentialLanguage.lean` | `caed20f55ee04b66b3401fbab3bd4df02284cdb74537cafcf937c60093db1758` |
| `PotentialRamsey.lean` | `800a962b4e670ae45899572328a360d7dad4af5073d68f0bde2328e1a0194867` |
| `EvenPotentialGauge.lean` | `7b19bcdae6720de2d832a129a1ac720a9585763f773864cadcbae1fd178e039a` |
| `PotentialGaugeHomogeneity.lean` | `c6dba623ef0c9779e242d3f336c0714cecbb23424bb70a057ac2b4743a4beb76` |
| `PotentialExpansionProperty.lean` | `1da5ce7c4dbe60b66a80e0137fc6e39aba49e49716658d2341df3319df6fba11` |
