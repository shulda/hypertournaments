# Independent review of cyclic strong amalgamation

Date: 2026-11-14. Reviewer: the CyclicRelation/CyclicLocalType agent,
independent of the author of CyclicAmalgamation. Mathematical source:
article commit `919349e7eceed3c7fa0ed126a337c6fae6624704`, the
four-constrained ternary cyclic-order case of the small-arity AP-to-SAP
assertion. This review does not concern the postponed five-constrained
ternary census.

Verdict: the reviewed module constructs an actual finite strong amalgam
for every span of orientation-preserving injections of finite cyclic
orders. The local-palette wrapper proves the same assertion for
`Admissible {2}` and obtains the base's admissibility from the preserved
left side. There is no remaining provider hypothesis or mathematical
blocker in this module. No proof source was changed during this review.

## Frozen snapshot

The requested author freeze agrees with the directly computed hash.
Hashes below identify the exact reviewed source and its relevant shared
dependencies; the root integration commit was not yet pinned by this review.

| Source | SHA256 |
| --- | --- |
| `Hypertournaments/CyclicAmalgamation.lean` | `438c6b745a3d16145c97ae69fe1a5a858155533e5d5732779848ffb567df7640` |
| `Hypertournaments/CircularHyper.lean` | `7e4c5bfa3975c2f692a96fd0b6761bcf625b0d20f642cde4524b4a7c7e39ed80` |
| `Hypertournaments/CircularCut.lean` | `2ba34f8d54d12977b2e11d875bbf32028fa47cfef3547849b3d6dc580e493ff2` |
| `Hypertournaments/CyclicRelation.lean` | `cfb25df5d256de03f094fb8d642307827bc36007b765b7e07cc146f2601ab906` |
| `Hypertournaments/CyclicLocalType.lean` | `4dd75cdf94af2cb4a81e0c0286f0e84dbbc43898a27092f8197bb4130bf70f3b` |
| `Hypertournaments/OrderedStrongSpan.lean` | `4effad2fef18631e4b78048e67af8b10428f937cdee9f883a6f9a74bd4b8823f` |
| `Hypertournaments/FiniteStrongSpan.lean` | `5ee0627d71ed79effd1391f2ef1b3bc025c31246ab901244b79ecd36c60861d0` |
| `Hypertournaments/OnePointNonmixedAdmissible.lean` | `3f8100a787bd4b32ff654ba7c95563650354636b7f719d3e027fb3cc1a25f72b` |

## Mathematical and API checks

1. `preserves_circularCompatible_of_strictMono` concludes the original
   `Preserves A B e`, with equality of Boolean orientation on every
   injective triple. It uses the full equivalence between orientation
   preservation and preservation of strict circular betweenness, then
   reflects all three strict comparisons through an increasing injection.
   Thus subsequent uses do not replace intrinsic embeddings by ordered
   embeddings in the theorem's input.

2. `Hyper.CircularCompatible.cut` cuts at a specified vertex and closes
   the resulting linear order using Mathlib's circularization. The
   `CircularOrder.cut_sbtw_iff` equivalence identifies the resulting strict
   circular relation with the original one on every triple. The cut
   retains the full carrier, including the distinguished root.

3. In `cyclic_span_linear_presentations`, a nonempty base supplies a root
   `p`; the side roots are exactly `f p` and `g p`. The original hypotheses
   `Preserves AA BB f` and `Preserves AA CC g` yield circular-relation
   preservation. `cutLinearOrder_strictMono` then proves that the original
   maps are increasing in these compatible cuts. Root cases in that
   helper are explicit; nonroot strict betweenness supplies the required
   distinctness. No increasing-map or compatible-root provider is assumed.

4. For an empty base, the sides choose linear presentations independently
   and both increasing-map obligations are vacuous. The linear-presentation
   helper explicitly treats the empty carrier: a linear order is lifted
   from `Fin (Fintype.card V)`, and compatibility is vacuous because no
   injective triple exists. Consequently an empty side, or both empty
   sides, is also included. Finiteness of the base is derived from its
   injection into the finite left side.

5. `cyclic_order_strong_span` uses exactly
   `FiniteStrongSpan.Carrier f g = B ⊕ {c : C // c ∉ Set.range g}`. Both
   output maps are the existing `FiniteStrongSpan.left f g` and
   `FiniteStrongSpan.right f g`; the proof does not change the original
   span or introduce extra vertices. The shuffle receives these maps,
   their actual injectivity proofs, and the implication supplied by the
   exact-overlap theorem. Closing the resulting order gives the actual
   `Hyper.ofCircularOrder` on this carrier, and strict monotonicity proves
   both intrinsic `Preserves` conclusions.

6. The fixed carrier supplies all strong-amalgamation facts independently
   of its orientations: `commutes` identifies the two copies of each base
   vertex; `overlap` states that these are precisely all cross-side
   identifications; `covers` says every target vertex comes from a side.
   Its `Finite` instance follows from finiteness of the two sides.

7. The final `cyclic_strong_span` wrapper assumes admissibility only for
   `BB` and `CC`. For every base four-tuple it transports the local index
   along `f` using `localIndex_preserves`, obtaining `Admissible {2} AA`.
   The proved `admissible_two_iff_isCyclicOrder` supplies all three circular
   certificates and returns admissibility of the actual output. There is
   no independent base-admissibility premise, omitted reconstruction, or
   unproved amalgamation provider.

## Independent verification

With the committed Lean 4.34.1 toolchain and pinned Mathlib, the independent
command `lake build Hypertournaments.CyclicAmalgamation` completed
successfully: 939 jobs, with no source warnings. Evidence is in the local
preparation log `cyclic-amalgamation-review-build.log`.

The separate Lean file `cyclic-amalgamation-review-axioms.lean` printed
axioms for all six declarations defined in the reviewed module:

- `preserves_circularCompatible_of_strictMono`;
- `Hyper.CircularCompatible.cut`;
- `Hyper.IsCyclicOrder.exists_linear_presentation`;
- `cyclic_span_linear_presentations`;
- `cyclic_order_strong_span`;
- `cyclic_strong_span`.

It additionally checked `OrderedStrongSpan.shuffle_orders` and the three
carrier theorems `FiniteStrongSpan.commutes`, `overlap`, and `covers`.
Every one of these ten declarations has exactly the standard axiom set
`propext, Classical.choice, Quot.sound`.

The same Lean file compiled independent usage checks combining the output
with commutation, exact overlap, and coverage; specializing the wrapper
to an empty base without a base-circle premise; specializing to an empty
left side; and obtaining a linear presentation of an arbitrary
hypertournament on `Empty`. The evidence file and its output are in the
local preparation directory as `cyclic-amalgamation-review-axioms.lean`
and `cyclic-amalgamation-review-axioms.log`.
