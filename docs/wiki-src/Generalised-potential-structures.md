# Generalised potential structures

Supplement: {{pdf:potentials}}.

This page connects *Generalised potential structures* to the affine-labelled
development. The supplement proves the generalised-potential theorem stated
in the [main article](Main-article), including strong amalgamation and a
precompact Ramsey expansion with the expansion property.

## Parameters and structures

The paper's raw arity is `n ≥ 3`. Lean writes `r` for the potential arity,
so **`n = r + 1`**. The fixed data are an involutive palette `Q`, an
additive commutative group `G`, an offset `a`, and a surjective map
`η : Q → G` satisfying `η(q*) = a − η(q)`. In even raw arity the offset
is zero. These are packaged by {{lean:Hypertournaments.Affine.Data}}.

The paper assumes that `Q` and `G` are finite. Several individual Lean
results need less: signed exactness and strong amalgamation do not require
finite palettes. The finite-palette assumptions remain present where they
are used for precompactness and the full expansion-property theorem.

{{lean:Hypertournaments.Affine.Labelled}} assigns labels to injective
ordered tuples. Odd coordinate permutations apply the chosen involution.
The raw structure is closed when `δ(η ∘ ω) = 0`, as expressed by
{{lean:Hypertournaments.Affine.Closed}}. A chosen potential satisfies
`δp = η ∘ ω`, as expressed by
{{lean:Hypertournaments.Affine.IsPotential}}. It has the affine permutation
rule with offset `a`; the lower switching gauge instead has offset zero.

Embeddings preserve **all raw labels**. Two different raw labels with the
same effective value are still distinguished. An
{{lean:Hypertournaments.Affine.Expansion}} additionally names one compatible
potential, and {{lean:Hypertournaments.Affine.toOrderedExpansion}} adds an
arbitrary linear order. Expanded embeddings preserve all three parts.

## Main interfaces

- {{lean:Hypertournaments.Affine.closed_iff_exists_potential}} gives the
  exact existence criterion for a potential.
- {{lean:Hypertournaments.Affine.expanded_ordered_strong_span}} constructs
  an actual strong amalgam retaining both side orders.
- {{lean:Hypertournaments.Affine.expansion_ordered_ramsey}} proves the
  Ramsey property in the language of the actual raw labels, potential
  labels and order.
- {{lean:Hypertournaments.Affine.ordered_expansions_finite}} proves
  precompactness on each fixed finite raw reduct.
- {{lean:Hypertournaments.Affine.expansion_property}} fixes one finite raw
  target before both source and target potentials and both orders are
  chosen.

The last quantifier order is important. An ordering-property target already
has a chosen potential; an expansion-property target fixes only the raw
reduct and must work for every compatible potential on it.

## How the proof is organized

1. Signed coboundaries and cone contraction give exactness and the switching
   description of differences between potentials. Start with
   {{file:Hypertournaments/Affine/SignedExactness.lean}} and
   {{file:Hypertournaments/Affine/Potential.lean}}.
2. Potentials are aligned on the common base before the raw structures are
   strongly amalgamated. The actual exact-overlap carrier is used in
   {{file:Hypertournaments/Affine/Amalgamation.lean}}. The chosen source
   potential and order can also be extended along a fixed raw embedding by
   {{lean:Hypertournaments.Affine.expansion_reasonable}}.
3. The Ramsey construction temporarily separates the potential labels from
   oriented upper codes and decodes its witness back to the original raw
   language. {{file:Hypertournaments/Affine/ExpansionCoding.lean}} records
   this bridge. Noninjective `η` is allowed: the proof retains one fixed
   target code when the compatible potential changes.
4. The expansion-property proof homogenizes a signed gauge. Its constant
   drift depends on the potential arity; the correction for odd potential
   arity is included in {{file:Hypertournaments/Affine/ExpansionProperty.lean}}.

For `Q = G = ZMod 2`, complementary raw labels, offset `1`, and odd raw
arity, the original even-hypertournament construction is recovered by
{{file:Hypertournaments/Affine/EvenSpecialization.lean}}.

## Paper-to-Lean correspondence

The display numbers below belong to the recorded source version. TeX labels
and full Lean declaration names are the stable references for future links
from the articles.

{{table:potentials}}
