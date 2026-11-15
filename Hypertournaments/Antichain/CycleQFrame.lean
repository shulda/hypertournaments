import Hypertournaments.Antichain.CycleCounting
import Hypertournaments.Antichain.CycleQ
import Mathlib.Tactic.FinCases

/-! The midpoint and isolated vertex of an induced `P₃ ⊔ K₁` are intrinsic. -/

namespace Hypertournaments.Antichain

theorem cycleQFrame_neighbors_card {N : ℕ} (hN : 8 ≤ N)
    (f : Fin 4 ↪ Fin N) (hf : cycleQFrame f) (i : Fin 4) :
    (cycleNeighbors {f 0, f 1, f 2, f 3} (f i)).card =
      if i = 1 then 2 else if i = 3 then 0 else 1 := by
  rcases hf with ⟨h01, h12, h02, h03, h13, h23⟩
  have h10 := (cycleAdj_symm (f 0) (f 1)).mp h01
  have h21 := (cycleAdj_symm (f 1) (f 2)).mp h12
  have h20 : ¬ cycleAdj (f 2) (f 0) := by rwa [cycleAdj_symm]
  have h30 : ¬ cycleAdj (f 3) (f 0) := by rwa [cycleAdj_symm]
  have h31 : ¬ cycleAdj (f 3) (f 1) := by rwa [cycleAdj_symm]
  have h32 : ¬ cycleAdj (f 3) (f 2) := by rwa [cycleAdj_symm]
  have hirr (j : Fin 4) := cycleAdj_irrefl (by omega : 2 ≤ N) (f j)
  fin_cases i <;>
    simp [cycleNeighbors, Finset.filter_insert, Finset.filter_singleton,
      h01, h12, h02, h03, h13, h23,
      h10, h21, h20, h30, h31, h32, hirr, f.injective.eq_iff]

theorem cycleQFrame_unique {N : ℕ} (hN : 8 ≤ N) (f g : Fin 4 ↪ Fin N)
    (hf : cycleQFrame f) (hg : cycleQFrame g)
    (hs : ({f 0, f 1, f 2, f 3} : Finset (Fin N)) = {g 0, g 1, g 2, g 3}) :
    f 1 = g 1 ∧ f 3 = g 3 := by
  have hcenter : (cycleNeighbors {f 0, f 1, f 2, f 3} (g 1)).card = 2 := by
    rw [hs]
    simpa using cycleQFrame_neighbors_card hN g hg 1
  have hisolate : (cycleNeighbors {f 0, f 1, f 2, f 3} (g 3)).card = 0 := by
    rw [hs]
    simpa using cycleQFrame_neighbors_card hN g hg 3
  have hm (i : Fin 4) : g i ∈ ({f 0, f 1, f 2, f 3} : Finset (Fin N)) := by
    rw [hs]
    fin_cases i <;> simp
  have hmid := hm 1
  have hiso := hm 3
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmid hiso
  constructor
  · rcases hmid with h | h | h | h
    · rw [h, cycleQFrame_neighbors_card hN f hf 0] at hcenter
      norm_num at hcenter
    · exact h.symm
    · rw [h, cycleQFrame_neighbors_card hN f hf 2] at hcenter
      norm_num at hcenter
    · rw [h, cycleQFrame_neighbors_card hN f hf 3] at hcenter
      norm_num at hcenter
  · rcases hiso with h | h | h | h
    · rw [h, cycleQFrame_neighbors_card hN f hf 0] at hisolate
      norm_num at hisolate
    · rw [h, cycleQFrame_neighbors_card hN f hf 1] at hisolate
      norm_num at hisolate
    · rw [h, cycleQFrame_neighbors_card hN f hf 2] at hisolate
      norm_num at hisolate
    · exact h.symm

end Hypertournaments.Antichain
