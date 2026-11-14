import Mathlib.Tactic.Ext
import Hypertournaments.FiniteHyperClass
import Hypertournaments.OnePointJoint

/-!
# Exact finite strong self-amalgams of local packets

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
class-level construction in `thm:higharity-no-eppa`. The hereditary
restriction has exactly n+2 vertices, with the two canonical packet copies.
-/

namespace Hypertournaments

theorem ClassHasStrongAmalgamation.self_amalgam_packet {n : ℕ}
    {K : FiniteHyperClass n} (hSAP : ClassHasStrongAmalgamation K)
    (hHer : ClassHereditary K) (P : Hyper n (Fin (n + 1))) (hP : P ∈ K (n + 1)) :
    ∃ D : Hyper n (Fin (n + 2)), D ∈ K (n + 2) ∧
      Preserves P D (leftJointInclusion n) ∧ Preserves P D (rightJointInclusion n) := by
  let base : Hyper n (Fin n) := P.pullback Fin.castSuccEmb
  have hbase : base ∈ K n := hHer base P Fin.castSuccEmb (fun _ => rfl) hP
  obtain ⟨d, C, i, j, hC, hi, hj, hcomm, hoverlap⟩ :=
    hSAP n (n + 1) (n + 1) base P P hbase hP hP
      Fin.castSuccEmb Fin.castSuccEmb (fun _ => rfl) (fun _ => rfl)
  have hne : i (Fin.last n) ≠ j (Fin.last n) := by
    intro hh
    obtain ⟨x, hx, _⟩ := hoverlap _ _ hh
    exact Fin.castSucc_ne_last x hx
  obtain ⟨h, hleft, hright⟩ := exists_joint_embedding n d i j hcomm hne
  let D := C.pullback h
  refine ⟨D, hHer D C h (fun _ => rfl) hC, ?_, ?_⟩
  · intro t
    have ht : (t.trans (leftJointInclusion n)).trans h = t.trans i := by
      ext k
      exact congrArg Fin.val (DFunLike.congr_fun hleft (t k))
    change C.orient ((t.trans (leftJointInclusion n)).trans h) = _
    rw [ht]
    exact hi t
  · intro t
    have ht : (t.trans (rightJointInclusion n)).trans h = t.trans j := by
      ext k
      exact congrArg Fin.val (DFunLike.congr_fun hright (t k))
    change C.orient ((t.trans (rightJointInclusion n)).trans h) = _
    rw [ht]
    exact hj t

end Hypertournaments
