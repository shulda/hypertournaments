import Hypertournaments.OddToggleP1SidePacketOrder

/-!
# Exact missing-old packet index geometry

An increasing side packet obtained by deleting old vertex v
enumerates all other old vertices in their original order, then
the new last vertex. We identify each old facet's true index by
the elementary explicit Fin.succAbove map, avoiding any assumption
about a hypothetical extension or alternate ordering.
-/

namespace Hypertournaments

/-- Every nonfinal facet of the genuine side packet corresponds
to a unique other old vertex w. Its finite packet position i is
w when w<v and w-1 when w>v. -/
theorem p1SidePacket_old_position
    (k : ℕ) (v : Fin (4*k+6))
    (hQ : (p1SidePacketOmitOld k v).card = 4*k+6)
    (i : Fin (4*k+6))
    (hi : i.val < 4*k+5) :
    ∃ w : Fin (4*k+6), w ≠ v ∧
      (p1SidePacketOmitOld k v).orderEmbOfFin hQ i = w.castSucc ∧
      (if w.val < v.val then w.val else w.val-1) = i.val := by
  have hp := p1SidePacket_orderEmb_eq_succAbove k v hQ i
  by_cases hlt : i.val < v.val
  · refine ⟨i, ?_, ?_, ?_⟩
    · intro he
      have hval := congrArg Fin.val he
      omega
    · have hcast : i.castSucc < v.castSucc := by
        change i.val < v.val
        exact hlt
      rw [hp]
      exact Fin.succAbove_of_castSucc_lt v.castSucc i hcast
    · simp only [if_pos hlt]
  · have hbound : i.val+1 < 4*k+6 := by omega
    let w : Fin (4*k+6) := ⟨i.val+1, hbound⟩
    refine ⟨w, ?_, ?_, ?_⟩
    · intro he
      have hval := congrArg Fin.val he
      dsimp [w] at hval
      omega
    · have hle : v.castSucc ≤ i.castSucc := by
        change v.val ≤ i.val
        omega
      have heq : v.castSucc.succAbove i = i.succ :=
        Fin.succAbove_of_le_castSucc v.castSucc i hle
      rw [hp, heq]
      apply Fin.ext
      rfl
    · have hnot : ¬ w.val < v.val := by
        dsimp [w]
        omega
      simp only [if_neg hnot]
      dsimp [w]

/-- The final increasing facet deletion is exactly the new last
side vertex, independently of the omitted old vertex. -/
theorem p1SidePacket_last_is_new
    (k : ℕ) (v : Fin (4*k+6))
    (hQ : (p1SidePacketOmitOld k v).card = 4*k+6) :
    (p1SidePacketOmitOld k v).orderEmbOfFin hQ
        (Fin.last (4*k+5)) = Fin.last (4*k+6) := by
  let i : Fin (4*k+6) := Fin.last (4*k+5)
  have hp := p1SidePacket_orderEmb_eq_succAbove k v hQ i
  have hle : v.castSucc ≤ i.castSucc := by
    change v.val ≤ 4*k+5
    have hv := v.isLt
    omega
  have heq : v.castSucc.succAbove i = i.succ :=
    Fin.succAbove_of_le_castSucc v.castSucc i hle
  rw [hp, heq]
  apply Fin.ext
  rfl

end Hypertournaments
