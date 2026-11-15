# Mathematical definitions

## Intrinsic orientations and embeddings

{{lean:Hypertournaments.Hyper}} encodes an `n`-hypertournament on a vertex
type `V`. Its `orient` field assigns a Boolean value to each injection
`Fin n ↪ V`. Swapping any two coordinates complements that value; the full
permutation law follows from this transposition law.

No order on `V` is part of this structure. A linear order is used when
presenting a sign table or naming a Ramsey expansion.

{{lean:Hypertournaments.Preserves}} says that a vertex injection preserves
the orientation of **every** injective ordered tuple. This is the embedding
notion throughout the finite classes. The relational encoding uses
orientation `false` as its positive relation. Sign tables in the
classification supplement have an explicit [catalogue dictionary](Classification)
when their bit-one convention is used.

## Forbidden families and pair cancellation

| Lean object | Mathematical meaning |
| --- | --- |
| {{lean:Hypertournaments.ForbiddenFamily}} | A set of forbidden structures on each `Fin m` |
| {{lean:Hypertournaments.Omits}} | No forbidden structure embeds by an orientation-preserving injection |
| {{lean:Hypertournaments.PairCancelling}} | A finite structure of arity at least three and size at least `n+1`, with nonconstant ordered links for every pair and every auxiliary linear order |

In the pair-cancellation condition, the two distinguished vertices occupy
the first two coordinates. Only the remaining coordinates are required to
increase in the auxiliary order. That order is quantified over; it does not
restrict the embeddings of the omission class.

Ordinary AP permits additional identifications between the two sides of an
amalgam. Strong AP requires their intersection to be exactly the image of
the original base. Both notions use arbitrary intrinsic embeddings.

## Local types and constraint levels

{{lean:Hypertournaments.localIndex}} is computed on an injective
`(n+1)`-tuple. Delete each coordinate in turn and normalize its facet bit
by the deletion-index parity. If `c` of the resulting bits are true, the
index is `min(c, n + 1 - c)`.

It is invariant under re-enumerating the vertex set and lies between zero
and `centralIndex n = (n+1)/2`, with natural-number division. For `n ≥ 2`,
it completely determines the isomorphism type on `n+1` vertices.
{{lean:Hypertournaments.Admissible}} requires every such packet to have an
index in the prescribed set.

{{lean:Hypertournaments.FiniteClass.KConstrained}} permits any defining
forbidden family whose structures have at most `k` vertices. The strict
hierarchy theorem rules out every alternative family of smaller constraints.
The [classification chapter](Classification) distinguishes normalized
four/five-vertex conditions from literal five-only conditions.

## Even orientations and potentials

{{lean:Hypertournaments.Hyper.IsEven}} says that the sum of the orientations
of all facets of each `(n+1)`-tuple is zero in `ZMod 2`.
{{lean:Hypertournaments.IsPotential}} expresses the actual tuple equation
`δφ = ω`, where the potential has arity one lower than the upper orientation.
For the even-hypertournament construction, the upper arity is odd and at
least three.

The generalized construction replaces the two labels by a finite involutive
palette and takes effective values in a finite abelian group. Its Lean
parameter `r` is the potential arity, so the paper's upper arity is `r+1`.
The [generalized-potential chapter](Generalised-potential-structures)
records the offset condition and the distinction between raw and effective
labels.

## EPPA and homogeneity

For a given injection `e`, `A.IsEPPAWitness B e` asserts that the whole
target `B` is finite, that `e` preserves the orientation, and that every
partial automorphism of `A` extends to an automorphism of `B` along `e`.
See {{lean:Hypertournaments.Hyper.IsEPPAWitness}}. The finite EPPA properties
quantify over witness structures in the required class.

{{lean:Hypertournaments.Hyper.Homogeneous}} says that two embeddings of the
same finite hypertournament into the structure are carried to one another
by an automorphism. The continuum construction produces countably infinite
structures with this property and identifies their exact finite ages.
