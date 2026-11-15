import Hypertournaments.Antichain.SumInduced
import Hypertournaments.Antichain.Rectangle
import Mathlib.Data.Finset.Sort

/-!
# Embeddings of sum-induced hypertournaments

This is the embedding reduction used in Sullivan's Lemma 4.7,
arXiv:2611.07292v1, proved here by four-set cancellation.

The difference between the two tournament edge functions is symmetric.
An embedding in arity `k` makes its sum zero on each `k`-set. Four-set
cancellation then shows that the same vertex injection preserves all
ternary orientations up to a single global reversal.
-/

namespace Hypertournaments.Antichain

universe u v

/-- Symmetric edge discrepancy associated with a vertex injection. -/
noncomputable def edgeDifference {V : Type u} {W : Type v}
    (T : Hyper 2 V) (U : Hyper 2 W) (e : V ↪ W) (x y : V) : ZMod 2 :=
  tournamentBit T x y + tournamentBit U (e x) (e y)

theorem edgeDifference_symm {V : Type u} {W : Type v}
    (T : Hyper 2 V) (U : Hyper 2 W) (e : V ↪ W) (x y : V) :
    edgeDifference T U e x y = edgeDifference T U e y x := by
  by_cases h : x = y
  · subst y
    rfl
  · have h' : e x ≠ e y := fun hh => h (e.injective hh)
    dsimp [edgeDifference]
    rw [tournamentBit_reverse T h, tournamentBit_reverse U h']
    have hh : ∀ a b : ZMod 2, a + b = (a + 1) + (b + 1) := by decide +kernel
    exact hh _ _

theorem pairSetSum_image_orderEmbedding {V W : Type*}
    [LinearOrder V] [LinearOrder W] (d : W → W → ZMod 2)
    (s : Finset V) (e : V ↪o W) :
    pairSetSum d (s.image e) = pairSetSum (fun x y => d (e x) (e y)) s := by
  classical
  unfold pairSetSum
  rw [Finset.sum_image (fun _ _ _ _ h => e.injective h)]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_image (fun _ _ _ _ h => e.injective h)]
  apply Finset.sum_congr rfl
  intro y hy
  simp only [OrderEmbedding.lt_iff_lt]

theorem pairSetSum_edgeDifference {n : ℕ} {V : Type*} {W : Type v}
    [LinearOrder V] (T : Hyper 2 V) (U : Hyper 2 W) (e : V ↪ W)
    (f : Fin n ↪o V) :
    pairSetSum (edgeDifference T U e) (Finset.univ.image f) =
      pairSum T f.toEmbedding + pairSum U (f.toEmbedding.trans e) := by
  rw [pairSetSum_image_orderEmbedding, pairSum_eq_sum, pairSum_eq_sum]
  unfold pairSetSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i < j <;> simp [hij, edgeDifference]

/-- An embedding of the higher-arity structures gives zero discrepancy on
every unordered set of the relevant size. -/
theorem edgeDifference_pairSetSum_zero {n : ℕ} {V : Type*} {W : Type v}
    [LinearOrder V] (T : Hyper 2 V) (U : Hyper 2 W) (e : V ↪ W)
    (he : Preserves (sumInduced T n) (sumInduced U n) e)
    (s : Finset V) (hs : s.card = n) : pairSetSum (edgeDifference T U e) s = 0 := by
  let f := s.orderEmbOfFin hs
  have hsum := congrArg bit (he f.toEmbedding)
  rw [sumInduced_orient, sumInduced_orient] at hsum
  have hh := pairSetSum_edgeDifference T U e f
  rw [Finset.image_orderEmbOfFin_univ] at hh
  rw [hh, hsum]
  simpa only [ZMod.neg_eq_self_mod_two] using add_neg_cancel (pairSum T f.toEmbedding)

/-- Higher-arity embeddings preserve the induced ternary orientation up to
one global reversal. The same vertex injection works on every triangle. -/
theorem sumInduced_embedding_triangle_difference {n : ℕ} {V : Type*} {W : Type v}
    [LinearOrder V] [Fintype V] (hn : 2 ≤ n) (hV : n + 2 ≤ Fintype.card V)
    (T : Hyper 2 V) (U : Hyper 2 W) (e : V ↪ W)
    (he : Preserves (sumInduced T n) (sumInduced U n) e) :
    ∃ c : ZMod 2, ∀ f : Fin 3 ↪ V,
      bit ((sumInduced U 3).orient (f.trans e)) =
        bit ((sumInduced T 3).orient f) + c := by
  obtain ⟨c, hc⟩ := triangleSum_constant (edgeDifference T U e)
    (edgeDifference_symm T U e) hn hV
    (edgeDifference_pairSetSum_zero T U e he)
  refine ⟨c, ?_⟩
  intro f
  rw [sumInduced_orient, sumInduced_orient]
  have hh : pairSum T f + pairSum U (f.trans e) = c := by
    rw [pairSum_three, pairSum_three]
    simpa only [triangleSum, edgeDifference, Function.Embedding.trans_apply,
      add_assoc, add_left_comm, add_comm] using hc f
  have hcancel : ∀ a b c : ZMod 2, a + b = c → b = a + c := by decide +kernel
  exact hcancel _ _ _ hh

end Hypertournaments.Antichain
