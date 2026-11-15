import Hypertournaments.PairAmalgamation

/-!
# Unbounded pair-cancelling omission classes

Strong amalgamation adds a fresh singleton to any admitted finite structure.
The size condition in pair cancellation ensures that the empty structure and
the singleton are admitted, even when the forbidden family is infinite.
-/

namespace Hypertournaments

theorem pair_cancelling_omission_unbounded {n : ℕ} (hn : 3 ≤ n)
    (family : ForbiddenFamily n)
    (hpc : ∀ m F, F ∈ family m → PairCancelling F) :
    ∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧ ∃ A : Hyper n (Fin m), Omits family A := by
  classical
  have small {m : ℕ} (hm : m < n + 1) (A : Hyper n (Fin m)) : Omits family A := by
    intro k F hF e _
    have hsize := (hpc k F hF).2.1
    have hle := Fintype.card_le_of_injective e e.injective
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hsize hle
    omega
  let E : Hyper n (Fin 0) := Hyper.fromOrderedSigns (fun _ => false)
  let U : Hyper n (Fin 1) := Hyper.fromOrderedSigns (fun _ => false)
  have hE : Omits family E := small (by omega) E
  have hU : Omits family U := small (by omega) U
  have empty_preserves {m : ℕ} (A : Hyper n (Fin m)) (e : Fin 0 ↪ Fin m) :
      Preserves E A e := by
    intro t
    exact Fin.elim0 (t ⟨0, by omega⟩)
  intro N
  induction N with
  | zero => exact ⟨0, Nat.zero_le _, E, hE⟩
  | succ N ih =>
    obtain ⟨m, hNm, A, hA⟩ := ih
    let f : Fin 0 ↪ Fin m := ⟨Fin.elim0, fun x => Fin.elim0 x⟩
    let g : Fin 0 ↪ Fin 1 := ⟨Fin.elim0, fun x => Fin.elim0 x⟩
    obtain ⟨d, D, i, j, hD, _, _, _, hoverlap⟩ :=
      pair_cancelling_hasStrongAmalgamation hn family hpc 0 m 1 E A U
        hE hA hU f g (empty_preserves A f) (empty_preserves U g)
    have hdisjoint : ∀ x y, i x ≠ j y := by
      intro x y heq
      obtain ⟨z, _⟩ := hoverlap x y heq
      exact Fin.elim0 z
    let e : Fin m ⊕ Fin 1 ↪ Fin d :=
      ⟨Sum.elim i j, by
        intro x y hxy
        cases x with
        | inl x => cases y with
          | inl y => exact congrArg Sum.inl (i.injective hxy)
          | inr y => exact False.elim (hdisjoint x y hxy)
        | inr x => cases y with
          | inl y => exact False.elim (hdisjoint y x hxy.symm)
          | inr y => exact congrArg Sum.inr (j.injective hxy)⟩
    have hcard := Fintype.card_le_of_injective e e.injective
    simp only [Fintype.card_sum, Fintype.card_fin] at hcard
    exact ⟨d, by omega, D, hD⟩

end Hypertournaments
