import Hypertournaments.OnePointJoint
import Hypertournaments.CanonicalPacket

/-!
# Canonical sorted one-point packets have their new vertex last

When the single fresh vertex is numbered Fin.last a, any
increasing (n+1)-packet containing it has the fresh vertex at
the LAST packet position. Every earlier packet position is
the canonical image of a unique old vertex in Fin a.

This is purely finite-order geometry, not an order expansion
of the hypertournament. It is the uniform transfer interface
needed to import old-packet singleton/occupancy calculations
into true fresh-containing one-point side packets.
-/

namespace Hypertournaments

/-- The maximal vertex of Fin(a+1), if contained in an increasing
packet, must occur at its final indexed position. -/
theorem p3CanonicalFresh_is_last_packet_position
    (a n : ℕ) (f : Fin (n+1) ↪o Fin (a+1))
    (hFresh : Fin.last a ∈ tupleVertices f.toEmbedding) :
    f (Fin.last n) = Fin.last a := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hFresh
  have hi' : f i = Fin.last a := by
    change f i = Fin.last a at hi
    exact hi
  by_cases hlast : i = Fin.last n
  · subst i
    exact hi'
  · have hlt : i < Fin.last n := by
      apply Fin.lt_def.mpr
      have hne : i.val ≠ n := by
        intro hv
        apply hlast
        apply Fin.ext
        exact hv
      have hv := i.isLt
      change i.val < n+1 at hv
      change i.val < n
      omega
    have hstrict := f.strictMono hlt
    rw [hi'] at hstrict
    have hv : (f (Fin.last n)).val < a+1 :=
      (f (Fin.last n)).isLt
    change a < (f (Fin.last n)).val at hstrict
    omega

/-- Every position before the last one in a sorted
fresh-containing packet is an old vertex, never the fresh. -/
theorem p3CanonicalPacket_old_position_ne_fresh
    (a n : ℕ) (f : Fin (n+1) ↪o Fin (a+1))
    (hFresh : Fin.last a ∈ tupleVertices f.toEmbedding)
    (i : Fin n) :
    f i.castSucc ≠ Fin.last a := by
  have hlast :=
    p3CanonicalFresh_is_last_packet_position a n f hFresh
  intro hi
  have hstrict : f i.castSucc < f (Fin.last n) :=
    f.strictMono (Fin.castSucc_lt_last i)
  rw [hlast, hi] at hstrict
  exact (lt_irrefl _) hstrict

/-- Each nonfresh packet vertex is in the canonical old-base
inclusion Fin a ↪ Fin(a+1), with its index specified exactly. -/
theorem p3CanonicalPacket_old_vertex_lift
    (a n : ℕ) (f : Fin (n+1) ↪o Fin (a+1))
    (hFresh : Fin.last a ∈ tupleVertices f.toEmbedding)
    (i : Fin n) :
    ∃ v : Fin a,
      (Fin.castSuccOrderEmb : Fin a ↪o Fin (a+1)) v =
        f i.castSucc := by
  have hne :=
    p3CanonicalPacket_old_position_ne_fresh a n f hFresh i
  have hv : (f i.castSucc).val < a := by
    have hbound := (f i.castSucc).isLt
    change (f i.castSucc).val < a+1 at hbound
    have hneVal : (f i.castSucc).val ≠ a := by
      intro hh
      apply hne
      apply Fin.ext
      exact hh
    omega
  let v : Fin a := ⟨(f i.castSucc).val, hv⟩
  refine ⟨v, ?_⟩
  apply Fin.ext
  rfl

end Hypertournaments
