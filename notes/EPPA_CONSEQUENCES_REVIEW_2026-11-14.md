# Independent review of the class-level EPPA consequences

## Source and reviewed scope

Source: `shulda/tex_hypertournaments` at
`919349e7eceed3c7fa0ed126a337c6fae6624704`,
`thm:higharity-no-eppa`, together with the class-level construction in
the expanded proof preparation. Reviewed modules:

- `FiniteHyperClass.lean`;
- `FourEqualPacket.lean`;
- `StrongSelfAmalgam.lean`;
- `PairCancellingWitnessClass.lean`;
- `EPPAConsequences.lean`.

No blocking mathematical or API issue was found. The conclusions use the
fully proved local obstruction, with all its hypotheses supplied by the
actual self-amalgam and equal-facet construction.

## Arbitrary hereditary classes and ordinary EPPA

`FiniteHyperClass` is a predicate on all finite presentations of the
original `Hyper` structures. It is not restricted to omission families.
`ClassHereditary` quantifies over arbitrary orientation-preserving vertex
injections. In particular, it includes closure under finite reindexing and
the induced-substructure restrictions used later in the proof.

`ClassHasStrongAmalgamation` has the original arbitrary-embedding span
interface and an exact-overlap clause. It assumes actual membership of
the three input structures and returns membership of the actual amalgam.
It does not replace general hereditary classes by a selected family of
local-index constraints.

`ClassHasEPPA` asks for a finite member of that same class containing the
input by an orientation-preserving injection, with the existing ordinary
`IsEPPAWitness` property. Its extensions are separate existential choices;
there is no coherence condition. An unrestricted finite-witness obstruction
therefore excludes this class-level ordinary EPPA property immediately.

Omission classes are supplied as proved instances: heredity is shown by
composing the actual preservation maps, and the SAP/EPPA interfaces agree
definitionally with the existing forbidden-family versions.

## Four equal facets and the distinguished vertex

`HasFourEqualFacets` explicitly chooses an injective four-tuple of packet
indices. Equality is stated for the actual normalized facet values.
The two Boolean color counts sum to n+1, so n≥6 gives four equal entries
by pigeonhole on at least seven entries. This step assumes no Ramsey theorem.

The numerical criterion `localIndex ≤ n-3` also suffices: the larger color
class then has at least four entries. Its helper retains the explicit n≥3
bound, while the local obstruction is used only at n≥4.

`reindex_four_equal_to_base` chooses a packet vertex outside the selected
four, possible because n+1≥5. It swaps that vertex with the final coordinate
and pulls the structure back along this actual permutation. The selected
four coordinates therefore lie in the first n entries, leaving the
distinguished final vertex outside them.

The permutation may be odd. The exact normalized-packet law complements
all values by the same bit; the proof applies that same complement to
both sides of the equal-value comparison. It does not incorrectly assume
that the reindexing preserves each normalized color or is an automorphism
of the unreindexed structure. Class membership of the pullback follows
from the stated hereditary embedding closure.

## Exactly n+2 vertices

`self_amalgam_packet` first restricts the packet to its first n vertices
and obtains that base's class membership by heredity. It strongly
self-amalgamates two copies of the packet over this base.

The exact-overlap clause is used to prove that the two new vertices are
distinct: identification would put a last coordinate in the image of
the base inclusion, which is impossible. Thus strongness is essential;
ordinary amalgamation alone is not silently substituted here.

The proved joint-numbering injection then embeds the canonical n+2-vertex
union into the ambient amalgam. Pulling the ambient orientation back along
this injection gives a structure on literal `Fin (n+2)`, and heredity puts
it in the original class. Both canonical packet inclusions are proved to
preserve all oriented tuples. The ambient amalgam may have extra vertices;
the output has exactly n+2 vertices regardless.

`exists_class_EPPA_obstruction_of_four_equal` supplies every hypothesis of
the local obstruction using this same structure: the two inclusions agree
on their common base, their final vertices are distinct, and the selected
four normalized base facets agree. No orientation involving both new
vertices is constrained or assumed.

## General class consequences

The local-index corollary is about an arbitrary actual packet P in the
class, not only a preferred representative. Its only numerical hypothesis
is the displayed `localIndex P ≤ n-3`; the usual validity bounds already
hold for every actual packet.

For an unbounded hereditary SAP class in arity at least six, unboundedness
supplies a member of size at least n+1. A literal finite injection selects
an n+1-vertex pullback in the class. The seven-entry pigeonhole lemma then
feeds the preceding construction. Thus the resulting obstruction is still
on exactly n+2 vertices and has no finite witness even outside the class.

`unbounded_hereditary_SAP_not_EPPA` and the numerical membership corollary
exclude `ClassHasEPPA`, the ordinary property defined above. Generality is
retained: neither theorem assumes that the class is an omission class,
has a chosen local palette, or satisfies an unproved provider condition.

## One witness for every pair-cancelling family

`allPairCancellingFamily n` contains all finite pair-cancelling structures,
in every finite cardinality. The existing arbitrary-family PC theorem
supplies its actual SAP, and its omission class is hereditary.

A packet of index at least q-1 omits this whole family. Indeed, any
forbidden structure embedding into an n+1-vertex packet has at least
n+1 vertices by the PC definition and at most n+1 by injectivity. It
therefore has exactly n+1 vertices, and its embedding is a permutation.
Preservation and the local permutation-invariance theorem identify its
index with the packet's index, contradicting the proved PC cutoff q-2.
This handles all forbidden sizes rather than only checking local ones.

The actual representative of index q-1 is consequently a member of this
common omission class. For n≥4, q-1≤n-3, so the numerical consequence gives
an n+2-vertex obstruction D omitting **all** finite PC structures.

`exists_common_pair_cancelling_EPPA_obstruction` chooses this D before
universally quantifying over the forbidden family. Every possibly infinite
PC family is a subfamily of the all-PC family, so the same D belongs to
each of its omission classes. Its unrestricted non-witness property is
retained unchanged. The final `pair_cancelling_not_EPPA` therefore covers
the empty family as well, yielding unrestricted non-EPPA in every arity
at least four. No assertion for arity two or three is made by that result.

## Independent validation and final snapshots

The independent combined five-target build passed (**1630 jobs**).
Standalone signature checks confirmed the general class quantifiers,
literal n+2 carriers, and the common-witness quantifier order. Additional
checks instantiated an arbitrary hereditary SAP/unbounded class at arity
six and an unrestricted arity-four obstruction/ordinary non-EPPA result.

Fourteen selected axiom checks all report only `propext`, `Classical.choice`
and `Quot.sound`. Evidence is in
`../preparation/eppa-consequences-independent-build.log` and
`../preparation/eppa-consequences-independent-axioms.log`.

The authors added explicit Ext/Omega imports before the final rebuild;
the mathematical statements and proofs were unchanged. Final SHA-256 hashes:

| Module | SHA-256 |
| --- | --- |
| `FiniteHyperClass.lean` | `36a177a23fe13367a576086be653168411492fe70d5b79519c070e058b2a98b3` |
| `FourEqualPacket.lean` | `7ab3fb2ec8be49c8d44a46855ed6827ce7840e3f5252097a78dd6fa71fd19fa4` |
| `StrongSelfAmalgam.lean` | `6da3b23db4cdc19a93fcc28ba7eec2ab7de708eb8b68f56249b1e7a386a55d4d` |
| `PairCancellingWitnessClass.lean` | `77f92034c8370da0e41cfe6d69a8cc7e597e321131fa78ed8ddfccc4351263ba` |
| `EPPAConsequences.lean` | `d9e36c02f47e5c25483b7200a55ed4a992b7bc7fec70ef8797bea2ecb67de904` |

No proof source was changed by this reviewer.
