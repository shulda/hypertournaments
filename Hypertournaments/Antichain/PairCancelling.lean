import Hypertournaments.Antichain.CycleLinkFlip
import Hypertournaments.Antichain.FinalTail
import Hypertournaments.Antichain.SumInduced

/-!
# Pair cancellation of the antichain members

Sullivan, `Ultrahomogeneous hypertournaments`, arXiv:2611.07292v1,
Lemma 4.3. We retain a generous size bound, since sharpness is irrelevant
to the infinite antichain.
-/

namespace Hypertournaments.Antichain

theorem tournamentBit_cycle {N : ℕ} {a b : Fin N} (hab : a ≠ b) :
    tournamentBit (cycleTournament N) a b = bit (cycleTournamentBit a b) := by
  rw [tournamentBit_of_ne _ hab]
  simp [cycleTournament_orient, Function.Embedding.embFinTwo_apply_zero,
    Function.Embedding.embFinTwo_apply_one]

/-- Summing the pointwise flip on a small prescribed set leaves one bit. -/
theorem exists_cycle_link_sum_flip {N : ℕ} (B : Finset (Fin N))
    (hB : B.Nonempty) (hN : 3 * B.card + 2 < N) :
    ∃ a c : Fin N, a ∉ B ∧ c ∉ B ∧
      (∑ b ∈ B, (tournamentBit (cycleTournament N) a b +
        tournamentBit (cycleTournament N) c b)) = 1 := by
  classical
  obtain ⟨a, c, r, ha, hc, hr, hflip⟩ := exists_cycle_link_flip B hB hN
  refine ⟨a, c, ha, hc, ?_⟩
  have hterm (b : Fin N) (hb : b ∈ B) :
      tournamentBit (cycleTournament N) a b + tournamentBit (cycleTournament N) c b =
        if b = r then 1 else 0 := by
    have hab : a ≠ b := fun h => ha (h.symm ▸ hb)
    have hcb : c ≠ b := fun h => hc (h.symm ▸ hb)
    rw [tournamentBit_cycle hab, tournamentBit_cycle hcb, ← bit_xor, hflip b hb]
    by_cases h : b = r <;> simp [h, bit]
  calc
    (∑ b ∈ B, (tournamentBit (cycleTournament N) a b +
      tournamentBit (cycleTournament N) c b)) =
        ∑ b ∈ B, if b = r then (1 : ZMod 2) else 0 :=
      Finset.sum_congr rfl hterm
    _ = 1 := by simp [hr]

private theorem cycle_sum_pairCancelling_aux (k N : ℕ) (hN : 4 * (k + 3) + 8 ≤ N)
    (order : LinearOrder (Fin N)) (u v : Fin N) (huv : u ≠ v) :
    ∃ f g : Fin (k + 3) ↪ Fin N,
      @IsPairLink (k + 3) (Fin N) order u v f ∧
      @IsPairLink (k + 3) (Fin N) order u v g ∧
      (sumInduced (cycleTournament N) (k + 3)).orient f ≠
        (sumInduced (cycleTournament N) (k + 3)).orient g := by
  classical
  let := order
  obtain ⟨t, hut, hvt, hfinal⟩ := exists_final_tail k u v huv (by simp; omega)
  let T := (Finset.univ : Finset (Fin k)).image t
  let B := insert u (insert v T)
  have hmemT (x : Fin N) : x ∈ T ↔ x ∈ Set.range t := by simp [T]
  have huT : u ∉ T := by simpa only [hmemT] using hut
  have hvT : v ∉ T := by simpa only [hmemT] using hvt
  have huins : u ∉ insert v T := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨huv, huT⟩
  have hBcard : B.card = k + 2 := by
    have hTcard : T.card = k := by simp [T, Finset.card_image_of_injective _ t.injective]
    change (insert u (insert v T)).card = k + 2
    rw [Finset.card_insert_of_notMem huins, Finset.card_insert_of_notMem hvT, hTcard]
  obtain ⟨a, c, ha, hc, hsum⟩ := exists_cycle_link_sum_flip B
    ⟨u, by simp [B]⟩ (by omega)
  have outside (x : Fin N) (hx : x ∉ B) :
      x ∉ Set.range t ∧ x ≠ u ∧ x ≠ v := by
    have hh : x ≠ u ∧ x ≠ v ∧ x ∉ T := by simpa [B] using hx
    exact ⟨(hmemT x).not.mp hh.2.2, hh.1, hh.2.1⟩
  let make (x : Fin N) (hx : x ∉ B) : Fin (k + 3) ↪ Fin N :=
    twoPadTuple (Fin.Embedding.cons t.toEmbedding (outside x hx).1) u v
      (not_mem_range_cons_of_not_mem t.toEmbedding u x hut (outside x hx).1
        (outside x hx).2.1.symm)
      (not_mem_range_cons_of_not_mem t.toEmbedding v x hvt (outside x hx).1
        (outside x hx).2.2.symm) huv
  have make0 (x : Fin N) (hx : x ∉ B) : make x hx 0 = u := by simp [make]
  have make1 (x : Fin N) (hx : x ∉ B) : make x hx 1 = v := by simp [make]
  have make2 (x : Fin N) (hx : x ∉ B) : make x hx 2 = x := by
    change twoPadTuple _ _ _ _ _ _ (0 : Fin (k + 1)).succ.succ = x
    rw [twoPadTuple_old]
    rfl
  have makeTail (x : Fin N) (hx : x ∉ B) (i : Fin k) :
      make x hx i.succ.succ.succ = t i := by
    change twoPadTuple _ _ _ _ _ _ i.succ.succ.succ = t i
    simp [Fin.Embedding.cons]
  have common (i : Fin (k + 3)) (hi : i ≠ 2) : make a ha i = make c hc i := by
    revert hi
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => Fin.cases ?_ (fun q => ?_) j) i) i
    · intro _; simp [make0]
    · intro _; simp [make1]
    · intro hi; exact (hi rfl).elim
    · intro _; simp [makeTail]
  have htwo : (2 : Fin (k + 3)).val = 2 := by
    change 2 % (k + 3) = 2
    exact Nat.mod_eq_of_lt (by omega)
  have hone : (1 : Fin (k + 3)).val = 1 := by
    change 1 % (k + 3) = 1
    exact Nat.mod_eq_of_lt (by omega)
  have image_make (x : Fin N) (hx : x ∉ B) :
      ((Finset.univ : Finset (Fin (k + 3))).erase 2).image (make x hx) = B := by
    ext y
    constructor
    · intro hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      have hi2 : i ≠ 2 := (Finset.mem_erase.mp hi).1
      revert hi2
      refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => Fin.cases ?_ (fun q => ?_) j) i) i
      · intro _; simp [make0, B]
      · intro _; simp [make1, B]
      · intro h; exact (h rfl).elim
      · intro _
        rw [makeTail x hx q]
        simp [B, T]
    · intro hy
      have hh : y = u ∨ y = v ∨ y ∈ T := by simpa [B] using hy
      rcases hh with rfl | rfl | hT
      · exact Finset.mem_image.mpr ⟨0, by
          simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          exact Fin.ne_of_val_ne (by rw [htwo]; change 0 ≠ 2; omega),
          make0 x hx⟩
      · exact Finset.mem_image.mpr ⟨1, by
          simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          exact Fin.ne_of_val_ne (by rw [hone, htwo]; omega),
          make1 x hx⟩
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hT
        exact Finset.mem_image.mpr ⟨i.succ.succ.succ, by
          simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          exact Fin.ne_of_val_ne (by rw [htwo]; simp only [Fin.val_succ]; omega),
          makeTail x hx i⟩
  refine ⟨make a ha, make c hc, ?_, ?_, ?_⟩
  · exact twoPad_cons_isPairLink t u v a hut hvt (outside a ha).1 huv
      (outside a ha).2.1 (outside a ha).2.2
      (hfinal a (outside a ha).2.1 (outside a ha).2.2 (outside a ha).1)
  · exact twoPad_cons_isPairLink t u v c hut hvt (outside c hc).1 huv
      (outside c hc).2.1 (outside c hc).2.2
      (hfinal c (outside c hc).2.1 (outside c hc).2.2 (outside c hc).1)
  · intro he
    have he' := congrArg bit he
    simp only [sumInduced_orient] at he'
    have hzero : pairSum (cycleTournament N) (make a ha) +
        pairSum (cycleTournament N) (make c hc) = 0 := by
      rw [he']
      exact (by decide : ∀ x : ZMod 2, x + x = 0) _
    rw [pairSum_exchange _ _ _ 2 common] at hzero
    have hs : (∑ i ∈ (Finset.univ : Finset (Fin (k + 3))).erase 2,
        (tournamentBit (cycleTournament N) (make a ha 2) (make a ha i) +
          tournamentBit (cycleTournament N) (make c hc 2) (make c hc i))) = 1 := by
      rw [← image_make a ha] at hsum
      rw [Finset.sum_image] at hsum
      · apply Eq.trans ?_ hsum
        apply Finset.sum_congr rfl
        intro i hi
        rw [make2 a ha, make2 c hc, common i (Finset.mem_erase.mp hi).1]
      · intro i hi j hj hij
        exact (make a ha).injective hij
    rw [hs] at hzero
    exact (by decide : (1 : ZMod 2) ≠ 0) hzero

/-- The cycle-twisted sum construction is genuinely pair-cancelling for
every auxiliary order. The relaxed numerical bound is uniform in the arity. -/
theorem cycle_sum_pairCancelling {n N : ℕ} (hn : 3 ≤ n) (hN : 4 * n + 8 ≤ N) :
    PairCancelling (sumInduced (cycleTournament N) n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  refine ⟨by omega, ?_, cycle_sum_pairCancelling_aux k N hN⟩
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  omega

end Hypertournaments.Antichain
