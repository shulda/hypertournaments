# Classification of constrained hypertournaments

Supplement: {{pdf:classification}}.

The classification supplement studies two finite local restriction problems. The first fixes an arity $n$ and allows selected isomorphism types on $n+1$ vertices. The second studies ternary hypertournaments with restrictions on four and five vertices. In both problems the classification concerns **unbounded classes**: there are finite members of arbitrarily large size.

Amalgamation uses arbitrary injective maps preserving orientation. The order used to display a sign table is a presentation device. Ordinary AP permits the two sides to acquire additional overlap; SAP requires their intersection to be exactly the image of the base.

## Local restrictions on n+1 vertices

Put $q=\lfloor(n+1)/2\rfloor$. The type $T_{n,d}$ is determined by the minority count $d$ in its normalized facet packet, with $0\le d\le q$. A palette $S$ gives the class of structures whose every $n+1$-vertex restriction has an index in $S$. This class is unbounded exactly when it allows the central type $q$.

The public classification is {{lean:Hypertournaments.amalgamation_classification_all_arities}}. For a valid palette containing the central type, the possibilities are:

| Arity | Precisely the palettes with AP | Strength of the positive result |
| --- | --- | --- |
| $n=2,3$ | Every palette containing $q$ | SAP |
| $n\ge4$ | $q-1\in S$, or $n$ odd and $S=E_n$ | SAP |

Here $E_n$ is the even/switching palette: the allowed indices have the parity of $q$. Lean calls it `switchingAllowed n`. The formal `ValidTypes n S` hypothesis excludes indices above $q$; the API also provides {{lean:Hypertournaments.unbounded_hasAP_iff_hasStrongAmalgamation}}, which tolerates such irrelevant indices.

The two positive constructions are constant-link amalgamation for pair-cancelling forbidden structures, and gluing potentials for even hypertournaments. Their Ramsey and expansion consequences are treated in the [Main article](Main-article).

## How the negative proof fits together

The public negative conclusion is {{lean:Hypertournaments.not_hasAP_of_excluded_types}}. Its proof constructs one-point-versus-one-point diagrams without ordinary amalgams.

1. Explicit finite seeds treat the negative palettes in arities four and five. The arity-four seeds have palettes $\{2\}$ and $\{0,2\}$; the arity-five seeds have palettes $\{3\}$, $\{0,3\}$, and $\{0,1,3\}$.
2. Two-coordinate suspensions raise the arity by two. A pigeonhole argument finds two auxiliary vertices with equal mixed profiles; slicing at them recovers a forbidden lower amalgam. The odd-arity suspension uses the link of a distinguished old vertex to control three-pad packets.
3. Two exceptional families remain. In arities $4k+5$, the zero-or-two principle for homogeneous packets gives {{lean:Hypertournaments.p1BadOnePoint_all}}. In arities $4k+3\ge7$, a finite counting argument gives {{lean:Hypertournaments.p3BadOnePoint_all}}.

The final induction has no outstanding exceptional-family hypothesis. Some intermediate modules expose reductions with such hypotheses; {{lean:Hypertournaments.p3OddOnePointObstructions}} and the explicit one-modulo-four construction supply their inputs. Side admissibility, impossibility of a joint structure, and failure of ordinary AP are separate stages. In particular, excluding a joint structure on distinct new vertices alone would not settle ordinary AP.

The formal suspensions use a larger auxiliary set than the sharp bound in the supplement. Profiles are recorded over all ordered injective tuples, rather than only the relevant unordered mixed sets. The source's optional contradiction-core bound is not needed by the classification. Likewise, the proof uses the concrete four-to-five cone seed and then suspensions; it does not package the general one-step cone construction as a separate Lean theorem. The correspondence table marks these proof variations explicitly.

Useful entry files are {{file:Hypertournaments/PositiveClassification.lean}}, {{file:Hypertournaments/NegativeClassification.lean}}, {{file:Hypertournaments/SmallArityClassification.lean}}, {{file:Hypertournaments/EvenOnePointWitness.lean}}, {{file:Hypertournaments/RootedOddOnePointWitness.lean}}, and {{file:Hypertournaments/OddToggleP3AllBadOnePoint.lean}}.

## Ternary restrictions on four and five vertices

There are three four-vertex types and twelve five-vertex types. A presentation has a four-palette $S_4$ and a five-palette $S_5$. It is **normalized** when $S_4$ consists exactly of the four-types appearing in the permitted five-types. Consistency, unboundedness, and ordinary AP force this normalization: {{lean:Hypertournaments.FiveConstrained.normalization_of_hasAP}}.

For normalized presentations, unboundedness is equivalent to allowing $P_0$, so there are $2^{11}=2048$ palettes to classify. Exactly five have AP, and each has SAP:

| Class | Allowed five-types | Required four-types | Five-palette mask |
| --- | --- | --- | ---: |
| Cyclic orders | $\{P_0\}$ | $\{C_4\}$ | 1 |
| Even | $\{P_0,P_8\}$ | $\{H_4,C_4\}$ | 257 |
| $H_4$-free | $\{P_0,P_1,P_2,P_4,P_5,P_6\}$ | $\{O_4,C_4\}$ | 119 |
| $P_9$-free | All except $P_9$ | All three | 3583 |
| Unrestricted | All twelve | All three | 4095 |

See {{lean:Hypertournaments.FiveConstrained.normalized_unbounded_amalgamation_classification}} for the normalized statement and {{lean:Hypertournaments.FiveConstrained.constrained_amalgamation_classification}} for separate consistent four/five prescriptions. The four-vertex column is part of each class definition.

For **literal five-only constraints**, every structure on fewer than five vertices is admitted. There are then exactly two unbounded AP classes: $P_9$-free and unrestricted. This is {{lean:Hypertournaments.FiveConstrained.five_only_hasAP_iff}}, with SAP supplied by {{lean:Hypertournaments.FiveConstrained.five_only_hasAP_iff_hasSAP}}. The distinction matters for the first three rows of the table.

## The finite certificates and the sign dictionary

The remaining 2043 normalized palettes are covered by 37 explicit one-point diagrams. {{lean:Hypertournaments.FiveConstrained.exists_certificate}} proves coverage. {{lean:Hypertournaments.FiveConstrained.certificateCheck_not_hasAP_of_bounded}} proves soundness for actual intrinsic amalgamation, including possible identification of the two new vertices and amalgams in larger targets. The combined interface is {{lean:Hypertournaments.FiveConstrained.normalized_not_hasAP}}.

The supplement displays a five-vertex mask by putting bit 1 on a **positive** increasing triple. `maskHyper` stores literal Boolean orientations, where this positive orientation is `false`. Consequently a displayed ten-bit mask $m$ is represented by `Nat.xor 1023 m`. Complementing the masks exchanges the catalogue labels $3\leftrightarrow7$ and $10\leftrightarrow11$. It fixes $P_9$, every induced four-type support, and all five positive palettes.

{{lean:Hypertournaments.FiveConstrained.sourcePositiveRepresentative_isomorphic}} realizes that dictionary by orientation-preserving vertex permutations. {{lean:Hypertournaments.FiveConstrained.sourceTypeToLean_positive_palette}} checks invariance of the positive masks, so the numerical masks in the classification table can be used directly. The dictionary is in {{file:Hypertournaments/FiveConstrained/SupplementCatalogue.lean}}.

The new positive example $P_9$ is pair-cancelling. Its omission class has SAP, freely ordered Ramsey expansions, and the ordering property through {{lean:Hypertournaments.FiveConstrained.p9_hasStrongAmalgamation}}, {{lean:Hypertournaments.FiveConstrained.p9_ordered_ramsey}}, and {{lean:Hypertournaments.FiveConstrained.p9_ordering_property}}.

## Correspondence with the supplement

The table follows the source's numbered statements. Rows for definitions, the finite catalogue, and certificate interfaces provide additional entry points. “Proof variant” records a changed auxiliary argument or an optimized bound that is not exported literally; the final classification theorems are proved.

{{table:classification}}
