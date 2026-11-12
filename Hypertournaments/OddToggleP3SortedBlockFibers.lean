import Hypertournaments.OddToggleP3ActualOccupancies
import Hypertournaments.CanonicalPacket

/-!
# Actual block fibers of canonical increasing old packets

For every old packet U, the unique increasing enumeration of its
vertices provides a monotone block-number word (since blocks
are consecutive in the old vertex order). Its fiber cardinalities
are EXACTLY the actual block occupancy statistics used by the p3
construction. Thus the numerical occupancy calculations transfer
without any arbitrary reordering to genuine sorted packet positions.

No random coefficients, age membership, or AP conclusion are used.
-/

namespace Hypertournaments

/-- The original numerical block labels of a canonically
increasing old packet are monotone along its vertex positions. -/
theorem p3SortedOldPacket_block_monotone
    {m t N : ℕ} (U : Finset (Fin (m*t)))
    (hU : U.card = N) :
    Monotone (fun j : Fin N =>
      p3BlockNumber t (U.orderEmbOfFin hU j)) := by
  intro i j hij
  have hle : (U.orderEmbOfFin hU i).val ≤
      (U.orderEmbOfFin hU j).val :=
    (U.orderEmbOfFin hU).monotone hij
  change (U.orderEmbOfFin hU i).val / t ≤
    (U.orderEmbOfFin hU j).val / t
  exact Nat.div_le_div_right hle

/-- The exact cardinality of the fiber at old block label i in
the increasing packet enumeration equals the true occupancy of
the corresponding subset U of the old base. -/
theorem p3SortedOldPacket_fiber_card_eq_occupancy
    (m t N : ℕ) (U : Finset (Fin (m*t)))
    (hU : U.card = N) (i : Fin m) :
    (Finset.univ.filter
      (fun j : Fin N => p3BlockNumber t
        (U.orderEmbOfFin hU j) = i.val)).card =
      p3BlockOccupancy m t U i := by
  classical
  let f : Fin N ↪o Fin (m*t) := U.orderEmbOfFin hU
  let pos : Finset (Fin N) :=
    Finset.univ.filter (fun j => p3BlockNumber t (f j) = i.val)
  have hset : pos.image f =
      U.filter (fun v => p3BlockNumber t v = i.val) := by
    ext v
    constructor
    · intro hv
      obtain ⟨j, hj, hfj⟩ := Finset.mem_image.mp hv
      have hjblock : p3BlockNumber t (f j) = i.val :=
        (Finset.mem_filter.mp hj).2
      have hjmem : f j ∈ U := by
        have hp : f j ∈ (Finset.univ : Finset (Fin N)).image f :=
          Finset.mem_image_of_mem f (Finset.mem_univ j)
        simpa only [f, Finset.image_orderEmbOfFin_univ U hU] using hp
      rw [← hfj]
      exact Finset.mem_filter.mpr ⟨hjmem, hjblock⟩
    · intro hv
      obtain ⟨hvU, hvblock⟩ := Finset.mem_filter.mp hv
      have hvimg : v ∈ (Finset.univ : Finset (Fin N)).image f := by
        simpa only [f, Finset.image_orderEmbOfFin_univ U hU] using hvU
      obtain ⟨j, _, hfj⟩ := Finset.mem_image.mp hvimg
      apply Finset.mem_image.mpr
      refine ⟨j, ?_, hfj⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa only [hfj] using hvblock
  calc
    (Finset.univ.filter
      (fun j : Fin N =>
        p3BlockNumber t (U.orderEmbOfFin hU j) = i.val)).card =
        pos.card := rfl
    _ = (pos.image f).card := (Finset.card_image_of_injective pos f.injective).symm
    _ = (U.filter (fun v => p3BlockNumber t v = i.val)).card := by rw [hset]
    _ = p3BlockOccupancy m t U i := rfl

end Hypertournaments
