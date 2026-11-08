# Source audit delta (v3 -> v4)

**Status:** human-readable AI proof note; not Lean-checked.

1. The normalized facet packet now has the explicit relabeling law
   `t'[π(i)] = sign(π) * t[i]`, with the induced-facet parity identity.
   The local type index is therefore an intrinsic isomorphism invariant.
2. Added a single exportable necessary-condition corollary, suitable for
   combining with the later positive AP theorem.
3. Clarified the identification branch of the two-coordinate reflection:
   recover n-orientations intrinsically by *prepending two distinct pads*
   to each injective n-tuple, rather than silently assuming a common
   ambient auxiliary order exists when new vertices are identified.
4. The Lean API explicitly needs a well-formed allowed type set. The
   current natural-index representation carries `ValidTypes n S`.
5. Heavy external proof dependencies: **none identified** beyond
   Mathlib-level finite combinatorics. The finite hypergraph Ramsey
   theorem remains contextual only and is not a premise of the
   formalization. The odd 3 mod 4 counting construction is the most
   expensive internal proof obligation.

The v4 note is a **proof-refactoring artifact**, not an independent
certification of the entire general-arity argument. In particular the
uniform parity/construction lemmas remain unformalized.
