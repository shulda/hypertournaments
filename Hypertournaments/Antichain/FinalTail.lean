import Hypertournaments.PairCancellation
import Hypertournaments.TwoPadIntrinsic

/-! # Final auxiliary-order tails -/

namespace Hypertournaments.Antichain

/-- After removing a prescribed pair, take the final `k` points of the
auxiliary order. Every other available point precedes the entire tail. -/
theorem exists_final_tail {V : Type*} [Fintype V] [LinearOrder V]
    (k : ℕ) (u v : V) (huv : u ≠ v) (hk : k + 2 ≤ Fintype.card V) :
    ∃ t : Fin k ↪o V, u ∉ Set.range t ∧ v ∉ Set.range t ∧
      ∀ a, a ≠ u → a ≠ v → a ∉ Set.range t → ∀ i, a < t i := by
  classical
  let U := ((Finset.univ : Finset V).erase u).erase v
  have hv : v ∈ ((Finset.univ : Finset V).erase u) := by simp [huv.symm]
  have hU : U.card = Fintype.card V - 2 := by
    simp only [U, Finset.card_erase_of_mem hv,
      Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ]
    omega
  have hkU : k ≤ U.card := by omega
  let e : Fin U.card ↪o V := U.orderEmbOfFin rfl
  let shift : Fin k ↪o Fin U.card :=
    OrderEmbedding.ofStrictMono
      (fun i => ⟨U.card - k + i.val, by omega⟩)
      (by intro i j hij; change U.card-k+i.val < U.card-k+j.val; omega)
  let t : Fin k ↪o V := shift.trans e
  have htU (i : Fin k) : t i ∈ U := Finset.orderEmbOfFin_mem U rfl (shift i)
  have huT : u ∉ Set.range t := by
    rintro ⟨i, hi⟩
    have := htU i
    simp only [U, Finset.mem_erase, Finset.mem_univ, and_true] at this
    exact this.2 hi
  have hvT : v ∉ Set.range t := by
    rintro ⟨i, hi⟩
    have := htU i
    simp only [U, Finset.mem_erase, Finset.mem_univ, and_true] at this
    exact this.1 hi
  refine ⟨t, huT, hvT, ?_⟩
  intro a hau hav hat i
  have haU : a ∈ U := by simp [U, hau, hav]
  have hae : a ∈ Set.range e := by
    simpa only [e, Finset.range_orderEmbOfFin, Finset.mem_coe] using haU
  obtain ⟨j, hj⟩ := hae
  have hjlt : j.val < U.card - k := by
    by_contra h
    have hjge : U.card - k ≤ j.val := by omega
    let q : Fin k := ⟨j.val - (U.card - k), by omega⟩
    have hq : shift q = j := by
      apply Fin.ext
      change U.card - k + (j.val - (U.card - k)) = j.val
      omega
    apply hat
    refine ⟨q, ?_⟩
    change e (shift q) = a
    rw [hq, hj]
  rw [← hj]
  change e j < e (shift i)
  apply e.strictMono
  change j.val < U.card - k + i.val
  omega

/-- Prepending the variable point to a final tail gives an increasing
tail after the prescribed distinguished pair. -/
theorem twoPad_cons_isPairLink {k : ℕ} {V : Type*} [LinearOrder V]
    (t : Fin k ↪o V) (u v a : V)
    (hu : u ∉ Set.range t) (hv : v ∉ Set.range t)
    (ha : a ∉ Set.range t) (huv : u ≠ v) (hau : a ≠ u) (hav : a ≠ v)
    (hat : ∀ i, a < t i) :
    IsPairLink u v
      (twoPadTuple (Fin.Embedding.cons t.toEmbedding ha) u v
        (not_mem_range_cons_of_not_mem t.toEmbedding u a hu ha hau.symm)
        (not_mem_range_cons_of_not_mem t.toEmbedding v a hv ha hav.symm) huv) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have he : i = 0 := Fin.ext hi
    subst i
    simp
  · intro i hi
    have he : i = 1 := Fin.ext hi
    subst i
    simp
  · intro i j hi hij
    obtain ⟨i', rfl⟩ : ∃ i' : Fin (k + 1), i = i'.succ.succ :=
      ⟨⟨i.val-2, by omega⟩, Fin.ext (by simp; omega)⟩
    obtain ⟨j', rfl⟩ : ∃ j' : Fin (k + 1), j = j'.succ.succ :=
      ⟨⟨j.val-2, by omega⟩, Fin.ext (by simp; omega)⟩
    simp only [twoPadTuple_old]
    have hlt : i' < j' := by change i'.val < j'.val; simpa using hij
    exact (Fin.strictMono_cons.mpr ⟨hat, t.strictMono⟩) hlt

end Hypertournaments.Antichain
