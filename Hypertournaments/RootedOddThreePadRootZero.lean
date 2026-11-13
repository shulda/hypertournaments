import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Hypertournaments.RootedOddThreePadRootPresent
import Hypertournaments.EvenPadOrderCount

/-!
# Canonical root 0 is the first old vertex in every h=3 packet

When the old root is vertex 0, its padded image has value exactly m.
In an increasing packet with exactly three pads all first three
vertices are below m, and every vertex from the fourth on is at
least m. Consequently, if the image of root 0 occurs, it must be
the fourth vertex. This supplies the exact geometric hypothesis of
the already established root-at-first-old centrality theorem.

The local-index corollary covers all root-present h=3 packets for
the canonical rooted odd suspension. The root-absent h=3 case
remains separate.
-/

namespace Hypertournaments

/-- For the canonical old root (value zero), an increasing packet
with three pads and containing the root has it at position three. -/
theorem rootedOdd_zero_root_first_old_of_threePads
    (k m a : ℕ)
    (root : Fin a) (hroot0 : root.val = 0)
    (f : Fin (2*k+4) ↪o Fin (m+a))
    (hthree :
      (evenPadProjection m a (tupleVertices f.toEmbedding)).card = 3)
    (hrootMem :
      root ∈ evenOldProjection m a (tupleVertices f.toEmbedding)) :
    f (⟨3, by omega⟩ : Fin (2*k+4)) =
      evenOldShift m a root := by
  let j3 : Fin (2*k+4) := ⟨3, by omega⟩
  have h3ge : m ≤ (f j3).val := by
    by_contra hh
    have hlt : (f j3).val < m := by omega
    have hindex := (evenPadProjection_ordered_prefix f j3).2 hlt
    rw [hthree] at hindex
    change (3 : ℕ) < 3 at hindex
    omega
  have hmem :
      evenOldShift m a root ∈ tupleVertices f.toEmbedding := by
    simpa only [evenOldProjection, Finset.mem_filter,
      Finset.mem_univ, true_and] using hrootMem
  obtain ⟨j, _, hj⟩ :
      ∃ j : Fin (2*k+4), j ∈ Finset.univ ∧
        f j = evenOldShift m a root := by
    exact Finset.mem_image.mp hmem
  have hjVal : (f j).val = m := by
    rw [hj]
    change m + root.val = m
    omega
  have hjge : 3 ≤ j.val := by
    by_contra hh
    have hjlt : j.val < 3 := by omega
    have hpad := (evenPadProjection_ordered_prefix f j).1
      (by rw [hthree]; exact hjlt)
    omega
  have hle : j3 ≤ j := by
    change (3 : ℕ) ≤ j.val
    exact hjge
  have hmon : f j3 ≤ f j := f.monotone hle
  have hupper : (f j3).val ≤ (f j).val := hmon
  apply Fin.ext
  change (f j3).val = m + root.val
  omega

/-- Every root-present three-pad local packet of the canonical-root
odd suspension has central local type, even when the old source
orientation is arbitrary. -/
theorem Hyper.rootedOddSuspension_localIndex_threePads_rootZero_present
    (k m a : ℕ) (A : Hyper (2*k+1) (Fin a))
    (root : Fin a) (hroot0 : root.val = 0)
    (f : Fin (2*k+4) ↪o Fin (m+a))
    (hthree :
      (evenPadProjection m a (tupleVertices f.toEmbedding)).card = 3)
    (hrootMem :
      root ∈ evenOldProjection m a (tupleVertices f.toEmbedding)) :
    localIndex (A.rootedOddSuspension m a root) f.toEmbedding =
      k+2 := by
  apply A.rootedOddSuspension_localIndex_threePads_root_at_first_old
    k m a root f hthree
  exact rootedOdd_zero_root_first_old_of_threePads
    k m a root hroot0 f hthree hrootMem

end Hypertournaments
