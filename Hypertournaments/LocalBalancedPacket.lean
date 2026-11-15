import Hypertournaments.TwoPadPacketCount
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Basic

/-!
# Reordering a packet to an alternating tail

A packet of size `k + 2` contains an alternating subpacket of size `k`
exactly when both signs occur at least `k / 2` times. The theorem here
gives an actual permutation of all coordinates, with only two entries
left outside the alternating tail.
-/

namespace Hypertournaments

/-- Equal positive counts of Boolean packets give a permutation
matching every coordinate, including both colour classes. -/
theorem exists_boolPacket_permutation_of_count_eq {m : ℕ}
    (bits target : Fin m → Bool)
    (hcount : boolPacketPositiveCount target = boolPacketPositiveCount bits) :
    ∃ σ : Equiv.Perm (Fin m), ∀ i, bits (σ i) = target i := by
  classical
  have hc : Fintype.card {i // target i = true} =
      Fintype.card {i // bits i = true} := by
    simpa only [Fintype.card_subtype, boolPacketPositiveCount] using hcount
  let ep : {i // target i = true} ≃ {i // bits i = true} :=
    Fintype.equivOfCardEq hc
  let en : {i // ¬target i = true} ≃ {i // ¬bits i = true} :=
    Fintype.equivOfCardEq (by simp only [Fintype.card_subtype_compl, hc])
  let σ := Equiv.subtypeCongr ep en
  refine ⟨σ, ?_⟩
  intro i
  by_cases hi : target i = true
  · have hh := (ep ⟨i, hi⟩).property
    simpa only [σ, Equiv.subtypeCongr, Equiv.trans_apply,
      Equiv.sumCompl_symm_apply_of_pos (p := fun x => target x = true) hi, Equiv.sumCongr_apply,
      Sum.map_inl, Equiv.sumCompl_apply_inl, hi] using hh
  · have hh := (en ⟨i, hi⟩).property
    have hσ : σ i = (en ⟨i, hi⟩).val := by
      simp only [σ, Equiv.subtypeCongr, Equiv.trans_apply,
        Equiv.sumCompl_symm_apply_of_neg (p := fun x => target x = true) hi, Equiv.sumCongr_apply,
        Sum.map_inr, Equiv.sumCompl_apply_inr]
    rw [hσ]
    cases hb : bits (en ⟨i, hi⟩).val <;> cases ht : target i <;>
      simp_all

private theorem balancedAlternating_count (k : ℕ) (b : Bool) :
    boolPacketPositiveCount (fun i : Fin k =>
      Bool.xor b (decide (i.val % 2 = 1))) =
        if b then k - k / 2 else k / 2 := by
  induction k generalizing b with
  | zero => simp [boolPacketPositiveCount]
  | succ k ih =>
    have htail (i : Fin k) :
        Bool.xor b (decide (i.succ.val % 2 = 1)) =
          Bool.xor (!b) (decide (i.val % 2 = 1)) := by
      have hpar : decide (i.succ.val % 2 = 1) =
          !decide (i.val % 2 = 1) := by
        simp only [Fin.val_succ]
        by_cases h : i.val % 2 = 1
        · have hh : (i.val + 1) % 2 ≠ 1 := by omega
          simp [h, hh]
        · have hh : (i.val + 1) % 2 = 1 := by omega
          simp [h, hh]
      rw [hpar]
      cases b <;> cases decide (i.val % 2 = 1) <;> rfl
    have heq :
        (fun i : Fin (k + 1) => Bool.xor b (decide (i.val % 2 = 1))) =
          Fin.cons b (fun i : Fin k => Bool.xor (!b) (decide (i.val % 2 = 1))) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simpa using htail j
    rw [heq, boolPacketPositiveCount_cons, ih]
    cases b <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ite_false, ite_true] <;> omega

/-- If neither colour class is too small, two coordinates can be
placed first so that all remaining colours alternate. -/
theorem exists_perm_alternating_tail {k : ℕ} (bits : Fin (k + 2) → Bool)
    (h : k / 2 ≤ min (boolPacketPositiveCount bits)
      (k + 2 - boolPacketPositiveCount bits)) :
    ∃ σ : Equiv.Perm (Fin (k + 2)), ∃ b : Bool, ∀ i : Fin k,
      bits (σ i.succ.succ) = Bool.xor b (decide (i.val % 2 = 1)) := by
  have hb := boolPacketPositiveCount_le bits
  have hex : ∃ a c b : Bool,
      (if a then 1 else 0) + (if c then 1 else 0) +
        (if b then k - k / 2 else k / 2) = boolPacketPositiveCount bits := by
    by_cases h0 : boolPacketPositiveCount bits = k / 2
    · exact ⟨false, false, false, by simp [h0]⟩
    by_cases h1 : boolPacketPositiveCount bits = k / 2 + 1
    · exact ⟨true, false, false, by simp [h1]; omega⟩
    by_cases h2 : boolPacketPositiveCount bits = k / 2 + 2
    · exact ⟨true, true, false, by simp [h2]; omega⟩
    refine ⟨true, true, true, ?_⟩
    simp only [ite_true]
    omega
  obtain ⟨a, c, b, hc⟩ := hex
  let target : Fin (k + 2) → Bool :=
    Fin.cons a (Fin.cons c (fun i : Fin k => Bool.xor b (decide (i.val % 2 = 1))))
  have hcount : boolPacketPositiveCount target = boolPacketPositiveCount bits := by
    simp only [target, boolPacketPositiveCount_two_cons, balancedAlternating_count]
    exact hc
  obtain ⟨σ, hσ⟩ := exists_boolPacket_permutation_of_count_eq bits target hcount
  exact ⟨σ, b, fun i => by simpa only [target, Fin.cons_succ] using hσ i.succ.succ⟩

end Hypertournaments
