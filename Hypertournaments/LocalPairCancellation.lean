import Hypertournaments.PairCancellation
import Hypertournaments.GeneralLocalIndexInvariant
import Hypertournaments.TwoPadIntrinsic

/-!
# Local types below the two central types are pair-cancelling

If all links through a fixed pair were constant, the normalized facets
obtained by deleting another vertex would alternate. Each sign would
then occur at least `centralIndex n - 1` times. This excludes precisely
the local types at most `centralIndex n - 2`.
-/

namespace Hypertournaments

private theorem alternatingPacket_count (k : ℕ) (b : Bool) :
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

private theorem alternatingTail_minority_lower_bound
    {k : ℕ} (bits : Fin (k + 2) → Bool) (b : Bool)
    (hbits : ∀ i : Fin k,
      bits i.succ.succ = Bool.xor b (decide (i.val % 2 = 1))) :
    k / 2 ≤ min (boolPacketPositiveCount bits)
      (k + 2 - boolPacketPositiveCount bits) := by
  have heq : bits = Fin.cons (bits 0) (Fin.cons (bits 1)
      (fun i : Fin k => Bool.xor b (decide (i.val % 2 = 1)))) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun t => ?_) j) i
    · rfl
    · rfl
    · simpa using hbits t
  rw [heq, boolPacketPositiveCount_two_cons, alternatingPacket_count]
  cases b <;> cases bits 0 <;> cases bits 1 <;>
    simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega

/-- There is a full tuple starting with any prescribed distinct pair,
whose tail follows the given auxiliary linear order. -/
theorem exists_pairFirstTuple {k : ℕ} {V : Type*} [Fintype V] [LinearOrder V]
    (hcard : Fintype.card V = k + 2) (u v : V) (huv : u ≠ v) :
    ∃ f : Fin (k + 2) ↪ V,
      f 0 = u ∧ f 1 = v ∧
      ∀ i j, 2 ≤ i.val → i < j → f i < f j := by
  classical
  let Q : Finset V := (Finset.univ.erase u).erase v
  have hvc : v ∈ (Finset.univ : Finset V).erase u := by
    simp [huv.symm]
  have hQ : Q.card = k := by
    simp only [Q, Finset.card_erase_of_mem hvc,
      Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ,
      hcard]
    omega
  let e : Fin k ↪o V := Q.orderEmbOfFin hQ
  have he (i : Fin k) : e i ∈ Q := by
    have hh : e i ∈ (Finset.univ : Finset (Fin k)).image e :=
      Finset.mem_image_of_mem _ (Finset.mem_univ i)
    simpa only [e, Finset.image_orderEmbOfFin_univ] using hh
  have hu : u ∉ Set.range e.toEmbedding := by
    rintro ⟨i, hi⟩
    have hm := he i
    simp only [Q, Finset.mem_erase, Finset.mem_univ, and_true] at hm
    exact hm.2 hi
  have hv : v ∉ Set.range e.toEmbedding := by
    rintro ⟨i, hi⟩
    have hm := he i
    simp only [Q, Finset.mem_erase, Finset.mem_univ, and_true] at hm
    exact hm.1 hi
  refine ⟨twoPadTuple e.toEmbedding u v hu hv huv, by simp, by simp, ?_⟩
  intro i j hi hij
  obtain ⟨i', rfl⟩ : ∃ i' : Fin k, i = i'.succ.succ := by
    exact ⟨⟨i.val - 2, by omega⟩, Fin.ext (by simp; omega)⟩
  obtain ⟨j', rfl⟩ : ∃ j' : Fin k, j = j'.succ.succ := by
    exact ⟨⟨j.val - 2, by omega⟩, Fin.ext (by simp; omega)⟩
  simp only [twoPadTuple_old]
  apply e.strictMono
  change i'.val < j'.val
  change i'.val + 1 + 1 < j'.val + 1 + 1 at hij
  omega

/-- Deleting a tail vertex from a pair-first tuple gives a genuine
link tuple with the same pair and the same auxiliary tail order. -/
theorem pairFirstTuple_facet_isPairLink
    {k : ℕ} {V : Type*} [LinearOrder V]
    (f : Fin (k + 2) ↪ V) (u v : V)
    (h0 : f 0 = u) (h1 : f 1 = v)
    (hmono : ∀ i j, 2 ≤ i.val → i < j → f i < f j)
    (a : Fin (k + 2)) (ha : 2 ≤ a.val) :
    IsPairLink u v (facet f a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have hlt : i.castSucc < a := by change i.val < a.val; omega
    change f (a.succAbove i) = u
    rw [Fin.succAbove_of_castSucc_lt _ _ hlt]
    have hi0 : i.castSucc = 0 := Fin.ext hi
    simpa only [hi0] using h0
  · intro i hi
    have hlt : i.castSucc < a := by change i.val < a.val; omega
    change f (a.succAbove i) = v
    rw [Fin.succAbove_of_castSucc_lt _ _ hlt]
    have hi1 : i.castSucc = 1 := Fin.ext hi
    simpa only [hi1] using h1
  · intro i j hi hij
    apply hmono
    · change 2 ≤ (a.succAbove i).val
      simp only [Fin.succAbove]
      split <;> simp only [Fin.val_castSucc, Fin.val_succ] <;> omega
    · exact Fin.strictMono_succAbove a hij

/-- A constant raw link forces both normalized signs to occur at least
`centralIndex n - 1` times in the full packet. -/
theorem localIndex_ge_of_constant_pairLink
    {k : ℕ} {V : Type*} (A : Hyper (k + 1) V)
    (f : Fin (k + 2) ↪ V) (b : Bool)
    (hraw : ∀ i : Fin k, A.orient (facet f i.succ.succ) = b) :
    centralIndex (k + 1) - 1 ≤ localIndex A f := by
  have hbits (i : Fin k) :
      normalizedFacet A f i.succ.succ =
        Bool.xor b (decide (i.val % 2 = 1)) := by
    unfold normalizedFacet
    rw [hraw i]
    have hm : i.succ.succ.val % 2 = i.val % 2 := by
      simp only [Fin.val_succ]
      omega
    rw [hm]
  have hh := alternatingTail_minority_lower_bound
    (fun i => normalizedFacet A f i) b hbits
  change (k + 1 + 1) / 2 - 1 ≤ _
  change k / 2 ≤ localIndex A f at hh
  have heq : (k + 1 + 1) / 2 - 1 = k / 2 := by omega
  rwa [heq]

/-- Every local type strictly below the two central types is
pair-cancelling, uniformly over all auxiliary orders of the vertices. -/
theorem pairCancelling_of_localIndex_le
    {n : ℕ} (hn : 3 ≤ n) (A : Hyper n (Fin (n + 1)))
    (hA : localIndex A (Function.Embedding.refl _) ≤ centralIndex n - 2) :
    PairCancelling A := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine ⟨hn, by simp, ?_⟩
  intro order u v huv
  let : LinearOrder (Fin (k + 1 + 1)) := order
  obtain ⟨f, h0, h1, hmono⟩ := exists_pairFirstTuple (k := k) (by simp) u v huv
  have hlink (i : Fin k) : IsPairLink u v (facet f i.succ.succ) :=
    pairFirstTuple_facet_isPairLink f u v h0 h1 hmono _ (by simp)
  by_contra h
  let i0 : Fin k := ⟨0, by omega⟩
  have hraw (i : Fin k) :
      A.orient (facet f i.succ.succ) = A.orient (facet f i0.succ.succ) := by
    by_contra hne
    exact h ⟨facet f i.succ.succ, facet f i0.succ.succ,
      hlink i, hlink i0, hne⟩
  have hlo := localIndex_ge_of_constant_pairLink A f _ hraw
  let σ : Equiv.Perm (Fin (k + 1 + 1)) := Equiv.ofBijective f
    ⟨f.injective, Finite.surjective_of_injective f.injective⟩
  have hperm := localIndex_perm_all A (Function.Embedding.refl _) σ
  have hemb : σ.toEmbedding.trans (Function.Embedding.refl _) = f := by rfl
  rw [hemb] at hperm
  have hq : 2 ≤ centralIndex (k + 1) := by unfold centralIndex; omega
  omega

end Hypertournaments
