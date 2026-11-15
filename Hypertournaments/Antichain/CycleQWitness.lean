import Hypertournaments.Antichain.CycleCounting
import Hypertournaments.Antichain.CycleQFrame
import Hypertournaments.Antichain.CycleWitnessFrame
import Hypertournaments.Antichain.CycleDegreeCount

/-! A copy of `P₃ ⊔ K₁` is uniquely specified by its midpoint and isolated
vertex. This connects the order-free four-subset count to the degree count. -/

namespace Hypertournaments.Antichain

theorem cycleQFrame_witness {N : ℕ} (hN : 8 ≤ N)
    {V : Finset (Fin N)} (f : Fin 4 ↪ Fin N) (hf : cycleQFrame f)
    (hsub : {f 0, f 1, f 2, f 3} ⊆ V) :
    f 1 ∈ cycleCenters V ∧ f 3 ∈ cycleFar V (f 1) ∧
      {f 0, f 1, f 2, f 3} = cycleQVertices (f 1) (f 3) := by
  rcases hf with ⟨h01, h12, h02, h03, h13, h23⟩
  have h10 := (cycleAdj_symm _ _).mp h01
  have h0 := (cycleAdj_iff_pred_succ (by omega : 3 ≤ N) (f 1) (f 0)).mp h10
  have h2 := (cycleAdj_iff_pred_succ (by omega : 3 ≤ N) (f 1) (f 2)).mp h12
  have hne02 : f 0 ≠ f 2 := fun h => by
    have := f.injective h
    exact (by decide : (0 : Fin 4) ≠ 2) this
  have hpair : ({f 0, f 2} : Finset (Fin N)) =
      {cyclePred (f 1), cycleSucc (f 1)} := by
    rcases h0 with h0 | h0 <;> rcases h2 with h2 | h2
    · exact (hne02 (h0.trans h2.symm)).elim
    · simp [h0, h2]
    · simp [h0, h2, Finset.pair_comm]
    · exact (hne02 (h0.trans h2.symm)).elim
  have hp : cyclePred (f 1) ∈ ({f 0, f 2} : Finset (Fin N)) := by
    rw [hpair]
    simp
  have hs : cycleSucc (f 1) ∈ ({f 0, f 2} : Finset (Fin N)) := by
    rw [hpair]
    simp
  have hmem (i : Fin 4) : f i ∈ V := by
    apply hsub
    fin_cases i <;> simp
  have hpV : cyclePred (f 1) ∈ V := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with h | h
    · rw [h]
      exact hmem 0
    · rw [h]
      exact hmem 2
  have hsV : cycleSucc (f 1) ∈ V := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with h | h
    · rw [h]
      exact hmem 0
    · rw [h]
      exact hmem 2
  have hpx : ¬ cycleAdj (cyclePred (f 1)) (f 3) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with h | h
    · simpa [h] using h03
    · simpa [h] using h23
  have hsx : ¬ cycleAdj (cycleSucc (f 1)) (f 3) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with h | h
    · simpa [h] using h03
    · simpa [h] using h23
  refine ⟨mem_cycleCenters.mpr ⟨hmem 1, hpV, hsV⟩,
    mem_cycleFar.mpr ⟨hmem 3, ?_, h13, hpx, hsx⟩, ?_⟩
  · intro h
    have := f.injective h
    exact (by decide : (3 : Fin 4) ≠ 1) this
  · ext z
    have hz := Finset.ext_iff.mp hpair z
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [cycleQVertices, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h | h | h)
      · rcases hz.mp (Or.inl h) with hp | hs
        · exact Or.inl hp
        · exact Or.inr (Or.inr (Or.inl hs))
      · exact Or.inr (Or.inl h)
      · rcases hz.mp (Or.inr h) with hp | hs
        · exact Or.inl hp
        · exact Or.inr (Or.inr (Or.inl hs))
      · exact Or.inr (Or.inr (Or.inr h))
    · rintro (h | h | h | h)
      · rcases hz.mpr (Or.inl h) with h0 | h2
        · exact Or.inl h0
        · exact Or.inr (Or.inr (Or.inl h2))
      · exact Or.inr (Or.inl h)
      · rcases hz.mpr (Or.inr h) with h0 | h2
        · exact Or.inl h0
        · exact Or.inr (Or.inr (Or.inl h2))
      · exact Or.inr (Or.inr (Or.inr h))

theorem cycleQVertices_subset {N : ℕ} {V : Finset (Fin N)} {a x : Fin N}
    (ha : a ∈ cycleCenters V) (hx : x ∈ cycleFar V a) : cycleQVertices a x ⊆ V := by
  have hc := mem_cycleCenters.mp ha
  have hf := mem_cycleFar.mp hx
  simp only [cycleQVertices, Finset.insert_subset_iff, Finset.singleton_subset_iff]
  exact ⟨hc.2.1, hc.1, hc.2.2, hf.1⟩

/-- The unlabelled four-subsets and the midpoint/isolated-vertex witnesses
are in bijection. -/
theorem cycleQCount_eq_witnessCount {N : ℕ} (hN : 8 ≤ N)
    (V : Finset (Fin N)) : cycleQCount V = cycleWitnessCount V := by
  classical
  unfold cycleQCount cycleWitnessCount
  symm
  apply Finset.card_bij (fun p _ => cycleQVertices p.1 p.2)
  · intro p hp
    rcases mem_cycleWitnesses.mp hp with ⟨ha, hx⟩
    rcases cycleWitness_frame hN ha hx with ⟨f, hset, hf, hfa, hfx⟩
    apply mem_cycleQCopies.mpr
    refine ⟨cycleQVertices_subset ha hx, ?_, ⟨f, hset.symm, hf⟩⟩
    rw [← hset]
    simp [f.injective.eq_iff]
  · intro p hp q hq hpq
    rcases mem_cycleWitnesses.mp hp with ⟨ha, hx⟩
    rcases mem_cycleWitnesses.mp hq with ⟨hb, hy⟩
    rcases cycleWitness_frame hN ha hx with ⟨f, hsetf, hf, hfa, hfx⟩
    rcases cycleWitness_frame hN hb hy with ⟨g, hsetg, hg, hga, hgy⟩
    have hu := cycleQFrame_unique hN f g hf hg (hsetf.trans (hpq.trans hsetg.symm))
    have hc : p.1 = q.1 := hfa.symm.trans (hu.1.trans hga)
    have hi : p.2 = q.2 := hfx.symm.trans (hu.2.trans hgy)
    exact Sigma.ext hc (heq_of_eq hi)
  · intro s hs
    rcases mem_cycleQCopies.mp hs with ⟨hsub, hcard, f, hset, hf⟩
    subst s
    have hw := cycleQFrame_witness hN f hf hsub
    refine ⟨⟨f 1, f 3⟩, mem_cycleWitnesses.mpr ⟨hw.1, hw.2.1⟩, ?_⟩
    exact hw.2.2.symm

/-- Exact count of the invariant in a complete cycle. -/
theorem cycleQCount_univ {N : ℕ} (hN : 8 ≤ N) :
    cycleQCount (Finset.univ : Finset (Fin N)) = N * (N - 5) := by
  rw [cycleQCount_eq_witnessCount hN]
  exact cycleWitnessCount_univ hN

/-- Every proper induced subgraph has strictly fewer copies than the cycle
on the same number of vertices. -/
theorem cycleQCount_lt {N : ℕ} (hN : 8 ≤ N)
    (V : Finset (Fin N)) (hV : V ≠ Finset.univ) (hm : 8 ≤ V.card) :
    cycleQCount V < V.card * (V.card - 5) := by
  rw [cycleQCount_eq_witnessCount hN]
  exact cycleWitnessCount_lt hN V hV hm

end Hypertournaments.Antichain
