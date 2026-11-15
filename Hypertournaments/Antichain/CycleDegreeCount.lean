import Hypertournaments.Antichain.CycleBoundary
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Tauto

/-!
# Counting cycle witnesses by their centres

Each centre excludes a window of five cycle vertices. Missing outer window
vertices contribute boundary errors. Each error of either orientation injects
into the non-centres, which suffices for a strict bound on sets of size at least
eight.
-/

open scoped BigOperators

namespace Hypertournaments.Antichain

theorem cyclePred_val {N : ℕ} (a : Fin N) :
    (cyclePred a).val = if a.val = 0 then N - 1 else a.val - 1 := by
  unfold cyclePred
  split_ifs <;> rfl

theorem cycleSucc_val {N : ℕ} (a : Fin N) :
    (cycleSucc a).val = if a.val + 1 = N then 0 else a.val + 1 := by
  unfold cycleSucc
  split_ifs <;> rfl

private theorem cycleWindow_distinct {N : ℕ} (hN : 8 ≤ N) (a : Fin N) :
    cyclePred (cyclePred a) ≠ cycleSucc (cycleSucc a) ∧
    cyclePred (cyclePred a) ≠ cyclePred a ∧
    cyclePred (cyclePred a) ≠ a ∧
    cyclePred (cyclePred a) ≠ cycleSucc a ∧
    cycleSucc (cycleSucc a) ≠ cyclePred a ∧
    cycleSucc (cycleSucc a) ≠ a ∧
    cycleSucc (cycleSucc a) ≠ cycleSucc a ∧
    cyclePred a ≠ a ∧ cyclePred a ≠ cycleSucc a ∧ a ≠ cycleSucc a := by
  have ha := a.isLt
  repeat' constructor
  all_goals
    simp only [ne_eq, Fin.ext_iff, cyclePred_val, cycleSucc_val]
    split_ifs <;> first | trivial | omega

def cycleWindow {N : ℕ} (a : Fin N) : Finset (Fin N) :=
  {cyclePred (cyclePred a), cycleSucc (cycleSucc a), cyclePred a, a, cycleSucc a}

theorem cycleFar_eq_sdiff_window {N : ℕ} (hN : 8 ≤ N)
    (V : Finset (Fin N)) (a : Fin N) :
    cycleFar V a = V \ cycleWindow a := by
  ext x
  simp only [mem_cycleFar, Finset.mem_sdiff, cycleWindow, Finset.mem_insert,
    Finset.mem_singleton, cycleAdj_iff_pred_succ (by omega : 3 ≤ N),
    cyclePred_cycleSucc (by omega : 2 ≤ N), cycleSucc_cyclePred (by omega : 2 ≤ N)]
  tauto

theorem cycleWindow_card {N : ℕ} (hN : 8 ≤ N) (a : Fin N) :
    (cycleWindow a).card = 5 := by
  obtain ⟨h12, h13, h14, h15, h23, h24, h25, h34, h35, h45⟩ :=
    cycleWindow_distinct hN a
  simp [cycleWindow, h12, h13, h14, h15, h23, h24, h25, h34, h35, h45]

theorem cycleFar_card_balance {N : ℕ} (hN : 8 ≤ N)
    (V : Finset (Fin N)) (a : Fin N) (ha : a ∈ cycleCenters V) :
    (cycleFar V a).card + 5 = V.card +
      (if cyclePred (cyclePred a) ∉ V then 1 else 0) +
      (if cycleSucc (cycleSucc a) ∉ V then 1 else 0) := by
  obtain ⟨h12, h13, h14, h15, h23, h24, h25, h34, h35, h45⟩ :=
    cycleWindow_distinct hN a
  obtain ⟨ha, hp, hs⟩ := mem_cycleCenters.mp ha
  rw [cycleFar_eq_sdiff_window hN]
  have hcard := Finset.card_sdiff_add_card_inter V (cycleWindow a)
  by_cases hpp : cyclePred (cyclePred a) ∈ V <;>
    by_cases hss : cycleSucc (cycleSucc a) ∈ V
  all_goals
    simp [cycleWindow, ha, hp, hs, hpp, hss,
      h12, h13, h14, h15, h23, h24, h25, h34, h35, h45] at hcard ⊢
    omega

@[simp] theorem cycleCenters_univ {N : ℕ} :
    cycleCenters (Finset.univ : Finset (Fin N)) = Finset.univ := by
  ext a
  simp

theorem cycleWitnessCount_eq_sum {N : ℕ} (V : Finset (Fin N)) :
    cycleWitnessCount V = ∑ a ∈ cycleCenters V, (cycleFar V a).card := by
  simp only [cycleWitnessCount, cycleWitnesses, Finset.card_sigma]

theorem cycleWitnessCount_univ {N : ℕ} (hN : 8 ≤ N) :
    cycleWitnessCount (Finset.univ : Finset (Fin N)) = N * (N - 5) := by
  have hrow (a : Fin N) : (cycleFar Finset.univ a).card = N - 5 := by
    have h := cycleFar_card_balance hN Finset.univ a (by simp)
    simp only [Finset.mem_univ, not_true_eq_false, ↓reduceIte,
      Finset.card_univ, Fintype.card_fin, add_zero] at h
    omega
  simp [cycleWitnessCount_eq_sum, hrow]

def cycleLeftErrors {N : ℕ} (V : Finset (Fin N)) : Finset (Fin N) :=
  (cycleCenters V).filter (fun a => cyclePred (cyclePred a) ∉ V)

def cycleRightErrors {N : ℕ} (V : Finset (Fin N)) : Finset (Fin N) :=
  (cycleCenters V).filter (fun a => cycleSucc (cycleSucc a) ∉ V)

theorem cycleLeftErrors_card_le {N : ℕ} (hN : 8 ≤ N) (V : Finset (Fin N)) :
    (cycleLeftErrors V).card ≤ V.card - (cycleCenters V).card := by
  have hInj : Function.Injective (@cyclePred N) := by
    intro a b hab
    simpa only [cycleSucc_cyclePred (by omega : 2 ≤ N)] using congrArg (@cycleSucc N) hab
  have hSub : (cycleLeftErrors V).image cyclePred ⊆ V \ cycleCenters V := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨ha, hmiss⟩ := Finset.mem_filter.mp ha
    refine Finset.mem_sdiff.mpr ⟨(mem_cycleCenters.mp ha).2.1, ?_⟩
    exact fun hp => hmiss (mem_cycleCenters.mp hp).2.1
  calc
    (cycleLeftErrors V).card = ((cycleLeftErrors V).image cyclePred).card :=
      (Finset.card_image_of_injective _ hInj).symm
    _ ≤ (V \ cycleCenters V).card := Finset.card_le_card hSub
    _ = V.card - (cycleCenters V).card :=
      Finset.card_sdiff_of_subset (Finset.filter_subset _ _)

theorem cycleRightErrors_card_le {N : ℕ} (hN : 8 ≤ N) (V : Finset (Fin N)) :
    (cycleRightErrors V).card ≤ V.card - (cycleCenters V).card := by
  have hInj : Function.Injective (@cycleSucc N) := by
    intro a b hab
    simpa only [cyclePred_cycleSucc (by omega : 2 ≤ N)] using congrArg (@cyclePred N) hab
  have hSub : (cycleRightErrors V).image cycleSucc ⊆ V \ cycleCenters V := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨ha, hmiss⟩ := Finset.mem_filter.mp ha
    refine Finset.mem_sdiff.mpr ⟨(mem_cycleCenters.mp ha).2.2, ?_⟩
    exact fun hs => hmiss (mem_cycleCenters.mp hs).2.2
  calc
    (cycleRightErrors V).card = ((cycleRightErrors V).image cycleSucc).card :=
      (Finset.card_image_of_injective _ hInj).symm
    _ ≤ (V \ cycleCenters V).card := Finset.card_le_card hSub
    _ = V.card - (cycleCenters V).card :=
      Finset.card_sdiff_of_subset (Finset.filter_subset _ _)

theorem cycleWitnessCount_balance {N : ℕ} (hN : 8 ≤ N) (V : Finset (Fin N)) :
    cycleWitnessCount V + 5 * (cycleCenters V).card =
      V.card * (cycleCenters V).card +
        (cycleLeftErrors V).card + (cycleRightErrors V).card := by
  have h := Finset.sum_congr rfl (fun a ha => cycleFar_card_balance hN V a ha)
  simpa only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
    Finset.sum_boole, Nat.cast_id, cycleLeftErrors, cycleRightErrors,
    ← cycleWitnessCount_eq_sum, Nat.mul_comm] using h

theorem cycleWitnessCount_lt {N : ℕ} (hN : 8 ≤ N)
    (V : Finset (Fin N)) (hV : V ≠ Finset.univ) (hm : 8 ≤ V.card) :
    cycleWitnessCount V < V.card * (V.card - 5) := by
  have hne : V.Nonempty := Finset.card_pos.mp (by omega)
  have hc := cycleCenters_card_lt (by omega : 3 ≤ N) hV hne
  have hleft := cycleLeftErrors_card_le hN V
  have hright := cycleRightErrors_card_le hN V
  have hbalance := cycleWitnessCount_balance hN V
  have hsub : V.card - (cycleCenters V).card + (cycleCenters V).card = V.card := by omega
  have hfive : V.card - 5 + 5 = V.card := by omega
  have hseven : V.card - 7 + 7 = V.card := by omega
  have hprod : 0 < (V.card - (cycleCenters V).card) * (V.card - 7) :=
    Nat.mul_pos (by omega) (by omega)
  nlinarith

end Hypertournaments.Antichain
