import Hypertournaments.Antichain.CycleCounting
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! # Enumerating a cycle witness as a four-vertex frame -/

namespace Hypertournaments.Antichain

/-- The midpoint and isolated vertex specify the canonical enumeration of
the induced path together with its isolated vertex. -/
theorem cycleWitness_frame {N : ℕ} (hN : 8 ≤ N) {V : Finset (Fin N)}
    {a x : Fin N} (_ha : a ∈ cycleCenters V) (hx : x ∈ cycleFar V a) :
    ∃ f : Fin 4 ↪ Fin N,
      ({f 0, f 1, f 2, f 3} : Finset (Fin N)) = cycleQVertices a x ∧
        cycleQFrame f ∧ f 1 = a ∧ f 3 = x := by
  have hpa : cyclePred a ≠ a := cyclePred_ne_self (by omega) a
  have hsa : cycleSucc a ≠ a := cycleSucc_ne_self (by omega) a
  have hps : cyclePred a ≠ cycleSucc a := cyclePred_ne_cycleSucc (by omega) a
  have hfar := mem_cycleFar.mp hx
  have hxa : x ≠ a := hfar.2.1
  have hxp : x ≠ cyclePred a := by
    intro h
    exact hfar.2.2.1 (h ▸ cycleAdj_pred (by omega) a)
  have hxs : x ≠ cycleSucc a := by
    intro h
    exact hfar.2.2.1 (h ▸ cycleAdj_succ (by omega) a)
  let f : Fin 4 ↪ Fin N := ⟨![cyclePred a, a, cycleSucc a, x], by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only at hij <;>
      first | rfl | exact (hpa hij).elim | exact (hpa hij.symm).elim |
        exact (hsa hij).elim | exact (hsa hij.symm).elim | exact (hps hij).elim |
        exact (hps hij.symm).elim | exact (hxa hij).elim | exact (hxa hij.symm).elim |
        exact (hxp hij).elim | exact (hxp hij.symm).elim | exact (hxs hij).elim |
        exact (hxs hij.symm).elim⟩
  refine ⟨f, rfl, ?_, rfl, rfl⟩
  change cycleAdj (cyclePred a) a ∧ cycleAdj a (cycleSucc a) ∧
    ¬ cycleAdj (cyclePred a) (cycleSucc a) ∧ ¬ cycleAdj (cyclePred a) x ∧
    ¬ cycleAdj a x ∧ ¬ cycleAdj (cycleSucc a) x
  exact ⟨(cycleAdj_symm a (cyclePred a)).mp (cycleAdj_pred (by omega) a),
    cycleAdj_succ (by omega) a, not_cycleAdj_pred_succ (by omega) a,
    hfar.2.2.2.1, hfar.2.2.1, hfar.2.2.2.2⟩

end Hypertournaments.Antichain
