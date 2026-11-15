import Hypertournaments.Antichain.CycleCounting
import Mathlib.Data.Finset.Max

/-!
# A proper induced cycle has a boundary vertex

A nonempty finite vertex set closed under both cyclic neighbours is the full
cycle. Thus a proper nonempty induced subgraph has fewer degree-two centres
than vertices.
-/

namespace Hypertournaments.Antichain

theorem eq_univ_of_cycle_closed {N : ℕ} (hN : 1 ≤ N)
    {V : Finset (Fin N)} (hne : V.Nonempty)
    (hpred : ∀ a ∈ V, cyclePred a ∈ V)
    (hsucc : ∀ a ∈ V, cycleSucc a ∈ V) : V = Finset.univ := by
  classical
  let a := V.min' hne
  have ha : a ∈ V := Finset.min'_mem V hne
  have ha0 : a.val = 0 := by
    by_contra hzero
    have hp := hpred a ha
    have hle := Finset.min'_le V (cyclePred a) hp
    change a.val ≤ (cyclePred a).val at hle
    simp only [cyclePred, hzero, ↓reduceDIte, Fin.val_mk] at hle
    omega
  have hzero : (⟨0, by omega⟩ : Fin N) ∈ V := by
    have heq : a = ⟨0, by omega⟩ := Fin.ext ha0
    exact heq ▸ ha
  have hall (j : ℕ) : ∀ hj : j < N, (⟨j, hj⟩ : Fin N) ∈ V := by
    induction j with
    | zero => intro _; exact hzero
    | succ j ih =>
      intro hj
      have hj' : j < N := by omega
      have hm := hsucc ⟨j, hj'⟩ (ih hj')
      have heq : cycleSucc (⟨j, hj'⟩ : Fin N) = ⟨j + 1, hj⟩ := by
        simp [cycleSucc, show j + 1 ≠ N by omega]
      exact heq ▸ hm
  apply Finset.eq_univ_of_forall
  intro x
  exact hall x.val x.isLt

theorem exists_noncenter_of_proper {N : ℕ} (hN : 1 ≤ N)
    {V : Finset (Fin N)} (hV : V ≠ Finset.univ) (hne : V.Nonempty) :
    ∃ a ∈ V, a ∉ cycleCenters V := by
  classical
  by_contra h
  have hfull : ∀ a ∈ V, a ∈ cycleCenters V := by
    intro a ha
    by_contra hnot
    exact h ⟨a, ha, hnot⟩
  apply hV
  apply eq_univ_of_cycle_closed hN hne
  · intro a ha
    exact (mem_cycleCenters.mp (hfull a ha)).2.1
  · intro a ha
    exact (mem_cycleCenters.mp (hfull a ha)).2.2

theorem cycleCenters_card_lt {N : ℕ} (hN : 3 ≤ N)
    {V : Finset (Fin N)} (hV : V ≠ Finset.univ) (hne : V.Nonempty) :
    (cycleCenters V).card < V.card := by
  obtain ⟨a, ha, hnot⟩ := exists_noncenter_of_proper (by omega : 1 ≤ N) hV hne
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro heq
  exact hnot (heq.symm ▸ ha)

end Hypertournaments.Antichain
