import Lean.Elab.Tactic.Omega
import Hypertournaments.FinitePresentation
import Mathlib.Order.WithBot
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Pair-cancellation and constant-link templates

Source: `tex_hypertournaments`, commit
`919349e7eceed3c7fa0ed126a337c6fae6624704`, pair-cancelling definition
and `prop:link-completion`; proof preparation section 3.

The auxiliary order only orders the tail after two fixed vertices. It is
quantified over in `PairCancelling`, rather than added to `Hyper` or `Preserves`.
-/

namespace Hypertournaments

/-- A tuple starting with `u,v`, with its remaining coordinates increasing.
The quantified index equations also make this definition meaningful in small arities. -/
def IsPairLink {n : ℕ} {V : Type*} [LinearOrder V]
    (u v : V) (f : Fin n ↪ V) : Prop :=
  (∀ i, i.val = 0 → f i = u) ∧
  (∀ i, i.val = 1 → f i = v) ∧
  (∀ i j, 2 ≤ i.val → i < j → f i < f j)

theorem IsPairLink.left_mem {n : ℕ} {V : Type*} [LinearOrder V]
    {u v : V} {f : Fin n ↪ V} (h : IsPairLink u v f) (hn : 2 ≤ n) :
    u ∈ tupleVertices f := by
  have h0 := h.1 ⟨0, by omega⟩ rfl
  exact Finset.mem_image.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, h0⟩

theorem IsPairLink.right_mem {n : ℕ} {V : Type*} [LinearOrder V]
    {u v : V} {f : Fin n ↪ V} (h : IsPairLink u v f) (hn : 2 ≤ n) :
    v ∈ tupleVertices f := by
  have h1 := h.2.1 ⟨1, by omega⟩ rfl
  exact Finset.mem_image.mpr ⟨⟨1, by omega⟩, Finset.mem_univ _, h1⟩

/-- A finite forbidden structure has nonconstant links for every pair and every
auxiliary order. The size and arity bounds are part of the mathematical definition. -/
def PairCancelling {n : ℕ} {V : Type*} (A : Hyper n V) : Prop :=
  3 ≤ n ∧ n + 1 ≤ Nat.card V ∧
  ∀ (order : LinearOrder V) (u v : V), u ≠ v →
    ∃ f g : Fin n ↪ V,
      @IsPairLink n V order u v f ∧ @IsPairLink n V order u v g ∧
      A.orient f ≠ A.orient g

/-- Put the distinguished vertices first, retaining the old order on all others. -/
private def pairKey {V : Type*} [DecidableEq V] (u v x : V) : WithBot (WithBot V) :=
  if x = u then ⊥ else if x = v then (⊥ : WithBot V) else ((x : WithBot V) : WithBot (WithBot V))

private theorem pairKey_injective {V : Type*} [LinearOrder V]
    (u v : V) (_huv : u ≠ v) : Function.Injective (pairKey u v) := by
  intro x y h
  by_cases hxu : x = u <;> by_cases hxv : x = v <;>
    by_cases hyu : y = u <;> by_cases hyv : y = v <;>
    simp_all [pairKey]

private def pairEmbedding {V : Type*} [LinearOrder V]
    (u v : V) (huv : u ≠ v) : V ↪ WithBot (WithBot V) :=
  ⟨pairKey u v, pairKey_injective u v huv⟩

private theorem pairKey_tail {n : ℕ} {V : Type*} [LinearOrder V]
    {u v : V} {f : Fin n ↪ V} (hn : 2 ≤ n) (h : IsPairLink u v f)
    (i : Fin n) (hi : 2 ≤ i.val) :
    pairKey u v (f i) = ((f i : WithBot V) : WithBot (WithBot V)) := by
  have h0 := h.1 ⟨0, by omega⟩ rfl
  have h1 := h.2.1 ⟨1, by omega⟩ rfl
  have hnu : f i ≠ u := by
    intro he
    have := f.injective (he.trans h0.symm)
    have hh : i.val = 0 := congrArg Fin.val this
    omega
  have hnv : f i ≠ v := by
    intro he
    have := f.injective (he.trans h1.symm)
    have hh : i.val = 1 := congrArg Fin.val this
    omega
  simp [pairKey, hnu, hnv]

private theorem pairEmbedding_strictMono {n : ℕ} {V : Type*} [LinearOrder V]
    {u v : V} (huv : u ≠ v) {f : Fin n ↪ V}
    (hn : 2 ≤ n) (h : IsPairLink u v f) :
    StrictMono (fun i => pairEmbedding u v huv (f i)) := by
  intro i j hij
  change pairKey u v (f i) < pairKey u v (f j)
  have hi_lt : i.val < j.val := hij
  by_cases hi0 : i.val = 0
  · rw [h.1 i hi0]
    by_cases hj1 : j.val = 1
    · rw [h.2.1 j hj1]
      simp [pairKey, huv.symm]
    · rw [pairKey_tail hn h j (by omega)]
      simp [pairKey]
  · by_cases hi1 : i.val = 1
    · rw [h.2.1 i hi1, pairKey_tail hn h j (by omega)]
      simp [pairKey, huv.symm]
    · rw [pairKey_tail hn h i (by omega), pairKey_tail hn h j (by omega)]
      exact WithBot.coe_lt_coe.mpr (WithBot.coe_lt_coe.mpr (h.2.2 i j (by omega) hij))

/-- A genuine total hypertournament with a constant zero link on `u,v`.
It is used only for tuples assigned to this missing pair in the completion. -/
def pairConstantTemplate {n : ℕ} {V : Type*} [LinearOrder V]
    (u v : V) (huv : u ≠ v) : Hyper n V :=
  (Hyper.fromOrderedSigns (n := n)
    (V := WithBot (WithBot V)) (fun _ => false)).pullback (pairEmbedding u v huv)

theorem pairConstantTemplate_orient {n : ℕ} {V : Type*} [LinearOrder V]
    {u v : V} (huv : u ≠ v) (hn : 2 ≤ n)
    (f : Fin n ↪ V) (h : IsPairLink u v f) :
    (pairConstantTemplate (n := n) u v huv).orient f = false := by
  exact fromOrderedSigns_orient_strictMono (fun _ => false)
    (f.trans (pairEmbedding u v huv)) (pairEmbedding_strictMono huv hn h)

end Hypertournaments
