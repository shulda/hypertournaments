import Hypertournaments.OddToggleP3SortedBlockFibers

/-!
# Distinct block labels in the sorted actual p3 old packet

If an old packet U meets every one of m base blocks except
possibly a designated label b, then the sorted block-number
word attains at least m-1 different labels. This proves the
actual finite occupancy-to-image-cardinality premise required
for the general repeated-edge bound.

No special probabilistic assumptions, no auxiliary order in
the hypertournament language, and no AP claim are used.
-/

namespace Hypertournaments

/-- A concrete packet meeting all m base blocks other than b
has at least m-1 distinct block labels in its canonical
increasing enumeration. -/
theorem p3SortedPacket_image_card_ge_of_all_but_one
    (m t N : ℕ)
    (U : Finset (Fin (m*t))) (hU : U.card = N)
    (missing : Fin m)
    (hOthers : ∀ i : Fin m, i ≠ missing →
      0 < p3BlockOccupancy m t U i) :
    m-1 ≤
      ((Finset.univ : Finset (Fin N)).image
        (fun j => p3BlockNumber t (U.orderEmbOfFin hU j))).card := by
  classical
  let otherBlocks : Finset (Fin m) :=
    Finset.univ.erase missing
  let B : Fin N → ℕ :=
    fun j => p3BlockNumber t (U.orderEmbOfFin hU j)
  have hOtherCard : otherBlocks.card = m-1 := by
    simp [otherBlocks]
  have hSubset :
      (otherBlocks.image (fun i : Fin m => i.val)) ⊆
      (Finset.univ : Finset (Fin N)).image B := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hDifferent : i ≠ missing := (Finset.mem_erase.mp hi).1
    have hpositive := hOthers i hDifferent
    have hNonempty :
        (U.filter (fun v => p3BlockNumber t v = i.val)).Nonempty := by
      have hh :
          0 < (U.filter (fun v => p3BlockNumber t v = i.val)).card :=
        hpositive
      exact Finset.card_pos.mp hh
    obtain ⟨v, hv⟩ := hNonempty
    have hvU : v ∈ U := (Finset.mem_filter.mp hv).1
    have hvB : p3BlockNumber t v = i.val :=
      (Finset.mem_filter.mp hv).2
    have hvimage :
        v ∈ (Finset.univ : Finset (Fin N)).image
              (U.orderEmbOfFin hU) := by
      simpa only [Finset.image_orderEmbOfFin_univ U hU] using hvU
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hvimage
    apply Finset.mem_image.mpr
    refine ⟨j, Finset.mem_univ _, ?_⟩
    change B j = i.val
    change U.orderEmbOfFin hU j = v at hj
    rw [hj]
    exact hvB
  have hNatInj : Function.Injective (fun i : Fin m => i.val) := by
    intro i j hij
    exact Fin.ext hij
  have hOtherImage :
      (otherBlocks.image (fun i : Fin m => i.val)).card =
        otherBlocks.card :=
    Finset.card_image_of_injective otherBlocks hNatInj
  calc
    m-1 = otherBlocks.card := hOtherCard.symm
    _ = (otherBlocks.image (fun i : Fin m => i.val)).card :=
      hOtherImage.symm
    _ ≤ ((Finset.univ : Finset (Fin N)).image B).card :=
      Finset.card_le_card hSubset

/-- In the q=m-1 one-fresh side-packet case, N=m+1 old vertices
and all but one base blocks represented give at least N-2
distinct labels. This is the exact quantitative premise used
by the six-edge duplicate selector. -/
theorem p3SortedPacket_qMinusOne_image_large
    (m t : ℕ)
    (U : Finset (Fin (m*t))) (hU : U.card = m+1)
    (missing : Fin m)
    (hOthers : ∀ i : Fin m, i ≠ missing →
      0 < p3BlockOccupancy m t U i) :
    (m+1)-2 ≤
      ((Finset.univ : Finset (Fin (m+1))).image
        (fun j => p3BlockNumber t (U.orderEmbOfFin hU j))).card := by
  have h := p3SortedPacket_image_card_ge_of_all_but_one
    m t (m+1) U hU missing hOthers
  omega

end Hypertournaments
