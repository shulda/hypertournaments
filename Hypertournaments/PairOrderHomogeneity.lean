import Hypertournaments.OrderedPair

/-!
Source: `tex_hypertournaments` at
`919349e7eceed3c7fa0ed126a337c6fae6624704`, `thm:ordering`.

# Pair-order homogeneity forces agreement or reversal

A homogeneous copy for the two-color comparison with a new linear order is
increasing or decreasing as a whole. All orders are explicit parameters, so
changing the target order never changes the native embedding hypothesis.
-/

universe v w

namespace Hypertournaments.Ramsey

open StructuralRamsey
open StructuralRamsey.Structure

/-- Whether the new target order agrees on the endpoints of an old ordered pair. -/
noncomputable def pairOrderColor {n : ℕ} {V : Type v}
    {C : Structure (orderedLanguage n) V} (newOrder : LinearOrder V)
    (e : Embedding (orderedPairModel n) C) : Bool := by
  classical
  exact decide (@LT.lt V newOrder.toLT (e 0) (e 1))

@[simp] theorem pairOrderColor_eq_true {n : ℕ} {V : Type v}
    {C : Structure (orderedLanguage n) V} (newOrder : LinearOrder V)
    (e : Embedding (orderedPairModel n) C) :
    pairOrderColor newOrder e = true ↔ @LT.lt V newOrder.toLT (e 0) (e 1) := by
  classical
  simp only [pairOrderColor, decide_eq_true_eq]

@[simp] theorem pairOrderColor_eq_false {n : ℕ} {V : Type v}
    {C : Structure (orderedLanguage n) V} (newOrder : LinearOrder V)
    (e : Embedding (orderedPairModel n) C) :
    pairOrderColor newOrder e = false ↔ ¬ @LT.lt V newOrder.toLT (e 0) (e 1) := by
  classical
  simp only [pairOrderColor, decide_eq_false_iff_not]

/-- Comparing all ordered pairs in a homogeneous native copy with a new target
order makes that copy globally monotone or globally antitone. -/
theorem pair_order_homogeneity {n : ℕ} (hn : 3 ≤ n)
    {U : Type v} {V : Type w} (D : Hyper n U) (oldD : LinearOrder U)
    (C : Hyper n V) (oldC newC : LinearOrder V)
    (baseline : Embedding (orderedPairModel n) (toOrderedNative D oldD))
    (f : Embedding (toOrderedNative D oldD) (toOrderedNative C oldC))
    (hhom : ∀ e₁ e₂ : Embedding (orderedPairModel n) (toOrderedNative D oldD),
      pairOrderColor newC (f.comp e₁) = pairOrderColor newC (f.comp e₂)) :
    (@StrictMono U V oldD.toPreorder newC.toPreorder f) ∨
      (@StrictAnti U V oldD.toPreorder newC.toPreorder f) := by
  let : LinearOrder U := oldD
  let : LinearOrder V := newC
  cases hc : pairOrderColor newC (f.comp baseline) with
  | false =>
    right
    intro x y hxy
    let e := orderedPairEmbedding hn D oldD x y hxy
    have he : pairOrderColor newC (f.comp e) = false := (hhom e baseline).trans hc
    have hnot := (pairOrderColor_eq_false newC (f.comp e)).mp he
    have hnot' : ¬ f x < f y := by
      simpa only [e, Embedding.comp_apply, orderedPairEmbedding_zero, orderedPairEmbedding_one] using hnot
    have hne : f y ≠ f x := by
      intro heq
      exact hxy.ne (f.injective heq).symm
    exact lt_of_le_of_ne (le_of_not_gt hnot') hne
  | true =>
    left
    intro x y hxy
    let e := orderedPairEmbedding hn D oldD x y hxy
    have he : pairOrderColor newC (f.comp e) = true := (hhom e baseline).trans hc
    have hlt := (pairOrderColor_eq_true newC (f.comp e)).mp he
    simpa only [e, Embedding.comp_apply, orderedPairEmbedding_zero, orderedPairEmbedding_one] using hlt

end Hypertournaments.Ramsey
