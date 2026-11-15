import Hypertournaments.Antichain.CycleH4
import Hypertournaments.Antichain.CycleQWitness
import Hypertournaments.Antichain.PairCancelling
import Hypertournaments.Antichain.SumInducedEmbedding
import Hypertournaments.ContinuumFamily

/-!
# The concrete infinite antichain

Sufficiently large cycle-twisted tournaments induce pair-cancelling
hypertournaments. Their four-vertex homogeneous packets recover the
cycle's copies of `P₃ ⊔ K₁`; counting those copies rules out embeddings
between distinct members of the sequence.
-/

namespace Hypertournaments.Antichain

theorem tupleVertices_trans {k : ℕ} {V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : Fin k ↪ V) (e : V ↪ W) :
    tupleVertices (f.trans e) = (tupleVertices f).image e := by
  ext x
  simp only [tupleVertices, Finset.mem_image, Finset.mem_univ, true_and,
    Function.Embedding.trans_apply]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨f i, ⟨i, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩

/-- The higher-arity orientation determines the cycle invariant on every
four-element subset, even for vertex injections that do not preserve order. -/
theorem cycleQ_image_iff_of_sumInduced_embedding {n N M : ℕ}
    (hn : 2 ≤ n) (hN : n + 2 ≤ N) (hM : 2 ≤ M)
    (e : Fin N ↪ Fin M)
    (he : Preserves (sumInduced (cycleTournament N) n)
      (sumInduced (cycleTournament M) n) e)
    (s : Finset (Fin N)) (hs : s.card = 4) :
    cycleQ (s.image e) ↔ cycleQ s := by
  obtain ⟨c, hc⟩ := sumInduced_embedding_triangle_difference hn
    (by simpa using hN) (cycleTournament N) (cycleTournament M) e he
  let f := (s.orderEmbOfFin hs).toEmbedding
  have hvs : tupleVertices f = s := Finset.image_orderEmbOfFin_univ s hs
  have hvt : tupleVertices (f.trans e) = s.image e := by
    rw [tupleVertices_trans, hvs]
  rw [← hvt, ← hvs, ← cycle_localIndex_zero_iff hM,
    ← cycle_localIndex_zero_iff (by omega : 2 ≤ N)]
  exact (localIndex_zero_iff_of_bit_shift (sumInduced (cycleTournament N) 3)
    (sumInduced (cycleTournament M) 3) e c hc f).symm

/-- Mapping an injection over finite subsets transports exactly the copies
of the four-vertex invariant. -/
theorem cycleQCopies_image_eq {N M : ℕ} (e : Fin N ↪ Fin M)
    (hQ : ∀ s : Finset (Fin N), s.card = 4 → (cycleQ (s.image e) ↔ cycleQ s)) :
    cycleQCopies (Finset.univ.image e) =
      (cycleQCopies (Finset.univ : Finset (Fin N))).image (fun s => s.image e) := by
  classical
  ext t
  constructor
  · intro ht
    obtain ⟨htsub, htcard, htQ⟩ := mem_cycleQCopies.mp ht
    let s : Finset (Fin N) := Finset.univ.filter (fun x => e x ∈ t)
    have hst : s.image e = t := by
      ext y
      constructor
      · rintro hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        exact (Finset.mem_filter.mp hx).2
      · intro hy
        obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp (htsub hy)
        refine Finset.mem_image.mpr ⟨x, ?_, hxy⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxy.symm ▸ hy⟩
    have hscard : s.card = 4 := by
      rw [← Finset.card_image_of_injective s e.injective, hst]
      exact htcard
    apply Finset.mem_image.mpr
    refine ⟨s, mem_cycleQCopies.mpr ⟨Finset.subset_univ _, hscard, ?_⟩, hst⟩
    exact (hQ s hscard).mp (hst.symm ▸ htQ)
  · intro ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hssub, hscard, hsQ⟩ := mem_cycleQCopies.mp hs
    apply mem_cycleQCopies.mpr
    refine ⟨Finset.image_subset_image hssub, ?_, (hQ s hscard).mpr hsQ⟩
    simpa only [Finset.card_image_of_injective _ e.injective] using hscard

theorem cycleQCount_image_eq {N M : ℕ} (e : Fin N ↪ Fin M)
    (hQ : ∀ s : Finset (Fin N), s.card = 4 → (cycleQ (s.image e) ↔ cycleQ s)) :
    cycleQCount (Finset.univ.image e) =
      cycleQCount (Finset.univ : Finset (Fin N)) := by
  unfold cycleQCount
  rw [cycleQCopies_image_eq e hQ]
  exact Finset.card_image_of_injective _ (Finset.image_injective e.injective)

/-- The two counting estimates force every sum-induced embedding to use the
whole target cycle. This isolates the counting comparison from its estimates. -/
theorem cycle_sum_embedding_card_eq_of_QCount {n N M : ℕ}
    (hn : 2 ≤ n) (hN : n + 2 ≤ N) (hlarge : 8 ≤ N) (hM : 8 ≤ M)
    (hfull : cycleQCount (Finset.univ : Finset (Fin N)) = N * (N - 5))
    (hbound : ∀ V : Finset (Fin M), V ≠ Finset.univ → 8 ≤ V.card →
      cycleQCount V < V.card * (V.card - 5))
    (e : Fin N ↪ Fin M)
    (he : Preserves (sumInduced (cycleTournament N) n)
      (sumInduced (cycleTournament M) n) e) : N = M := by
  classical
  have hcard : (Finset.univ.image e).card = N := by
    rw [Finset.card_image_of_injective _ e.injective]
    exact Finset.card_fin N
  have hcount := cycleQCount_image_eq e
    (cycleQ_image_iff_of_sumInduced_embedding hn hN (by omega) e he)
  by_contra hne
  have hproper : Finset.univ.image e ≠ Finset.univ := by
    intro hh
    have hc := congrArg Finset.card hh
    rw [hcard, Finset.card_fin] at hc
    exact hne hc
  have hstrict := hbound (Finset.univ.image e) hproper (by rwa [hcard])
  rw [hcard, hcount, hfull] at hstrict
  exact (Nat.lt_irrefl _) hstrict

/-- Distinct sufficiently large cycle-twisted structures do not embed into
one another. -/
theorem cycle_sum_embedding_card_eq {n N M : ℕ} (hn : 3 ≤ n)
    (hN : 4 * n + 8 ≤ N) (hM : 4 * n + 8 ≤ M)
    (e : Fin N ↪ Fin M)
    (he : Preserves (sumInduced (cycleTournament N) n)
      (sumInduced (cycleTournament M) n) e) : N = M := by
  exact cycle_sum_embedding_card_eq_of_QCount (by omega) (by omega)
    (by omega) (by omega) (cycleQCount_univ (by omega))
    (fun V hV hm => cycleQCount_lt (by omega) V hV hm) e he

/-- A concrete infinite embedding antichain of pair-cancelling structures.
The generous size bound avoids irrelevant small boundary cases. -/
noncomputable def cycleIndexedPCAntichain (n : ℕ) (hn : 3 ≤ n) :
    IndexedPCAntichain n where
  member i := ⟨i + 4 * n + 8, sumInduced (cycleTournament (i + 4 * n + 8)) n⟩
  pairCancelling i := cycle_sum_pairCancelling hn (by omega)
  incomparable i j h := by
    obtain ⟨e, he⟩ := h
    have hij := cycle_sum_embedding_card_eq
      (N := i + 4 * n + 8) (M := j + 4 * n + 8) hn (by omega) (by omega) e he
    omega

end Hypertournaments.Antichain
