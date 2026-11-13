import Hypertournaments.OddToggleP3FreshOldMembership
import Hypertournaments.OddToggleP3ActualOccupancies

/-!
# Transfer genuine old-block occupancy zeros and positives to actual packets

The canonical one-fresh packet order theorem identifies its
old-base subset U *exactly* by
 v in U <-> v.castSucc in packet.
The true occupancy statistics are cardinalities of the filters
of this subset by block label. Thus occupancy zero means the
packet has no old vertex of that block, and positive occupancy
produces an actual old packet vertex of the corresponding label.

These are the local finite-set bridges needed to convert the
exhaustive three-way occupancy case split into the premises
of the already kernel-proved q=m-1, two-missing, and pending
q=m actual side-age lemmas. No random W,L assumptions.
-/

namespace Hypertournaments

/-- An absent actual block fiber in the exact old part U of
a canonical one-fresh packet is absent from the real packet. -/
theorem p3CanonicalFresh_zero_occupancy_is_missing
    (m t : ℕ)
    (U : Finset (Fin (m*t)))
    (f : Fin ((m+1)+1) ↪o Fin (m*t+1))
    (hMem : ∀ v : Fin (m*t),
      v ∈ U ↔ v.castSucc ∈ tupleVertices f.toEmbedding)
    (i : Fin m)
    (hzero : p3BlockOccupancy m t U i = 0) :
    ∀ v : Fin (m*t),
      v.castSucc ∈ tupleVertices f.toEmbedding →
      p3BlockNumber t v ≠ i.val := by
  classical
  have hFilterZero :
      U.filter (fun v => p3BlockNumber t v = i.val) = ∅ := by
    apply Finset.card_eq_zero.mp
    exact hzero
  intro v hv hblock
  have hvU : v ∈ U := (hMem v).mpr hv
  have hvFilter :
      v ∈ U.filter (fun z => p3BlockNumber t z = i.val) :=
    Finset.mem_filter.mpr ⟨hvU,hblock⟩
  rw [hFilterZero] at hvFilter
  simp at hvFilter

/-- Every positively occupied block fiber is represented by a
real old packet vertex with the corresponding exact block label. -/
theorem p3CanonicalFresh_positive_occupancy_witness
    (m t : ℕ)
    (U : Finset (Fin (m*t)))
    (f : Fin ((m+1)+1) ↪o Fin (m*t+1))
    (hMem : ∀ v : Fin (m*t),
      v ∈ U ↔ v.castSucc ∈ tupleVertices f.toEmbedding)
    (i : Fin m)
    (hpositive : 0 < p3BlockOccupancy m t U i) :
    ∃ v : Fin (m*t),
      v.castSucc ∈ tupleVertices f.toEmbedding ∧
      p3BlockNumber t v = i.val := by
  classical
  have hNonempty :
      (U.filter (fun v => p3BlockNumber t v = i.val)).Nonempty := by
    apply Finset.card_pos.mp
    exact hpositive
  obtain ⟨v,hv⟩ := hNonempty
  obtain ⟨hvU,hblock⟩ := Finset.mem_filter.mp hv
  exact ⟨v, (hMem v).mp hvU, hblock⟩

end Hypertournaments
