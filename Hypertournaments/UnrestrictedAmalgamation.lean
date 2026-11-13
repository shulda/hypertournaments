import Hypertournaments.PairCompletion
import Hypertournaments.PartialAmalgam
import Hypertournaments.OrderedStrongSpan

/-!
# Unrestricted strong amalgamation, including tournaments

There are no forbidden configurations. The actual partial-union and
same-carrier completion constructions therefore apply in every arity at least
two, including the binary case needed for ternary switching potentials.
-/

universe u v w

namespace Hypertournaments

/-- The omission class of this family is the class of all hypertournaments. -/
def emptyForbiddenFamily (n : ℕ) : ForbiddenFamily n := fun _ => ∅

theorem emptyForbiddenFamily_pairCancelling (n : ℕ) :
    ∀ m (F : Hyper n (Fin m)), F ∈ emptyForbiddenFamily n m → PairCancelling F := by
  intro m F h
  exact False.elim h

theorem omits_emptyForbiddenFamily {n : ℕ} {V : Type u} (A : Hyper n V) :
    Omits (emptyForbiddenFamily n) A := by
  intro m F h
  exact False.elim h

/-- A genuine unrestricted strong amalgam on the exact-overlap carrier of
arbitrary finite sides. No nonempty-base or omission hypothesis is required. -/
theorem unrestricted_strong_span {n : ℕ} (hn : 2 ≤ n)
    {A : Type u} {B : Type v} {C : Type w} [Finite B] [Finite C]
    (AA : Hyper n A) (BB : Hyper n B) (CC : Hyper n C)
    (f : A ↪ B) (g : A ↪ C) (hAB : Preserves AA BB f) (hAC : Preserves AA CC g) :
    ∃ D : Hyper n (FiniteStrongSpan.Carrier f g),
      Preserves BB D (FiniteStrongSpan.left f g) ∧
      Preserves CC D (FiniteStrongSpan.right f g) := by
  classical
  let : Fintype B := Fintype.ofFinite B
  let : Fintype C := Fintype.ofFinite C
  let e := Fintype.equivFin (FiniteStrongSpan.Carrier f g)
  let : LinearOrder (FiniteStrongSpan.Carrier f g) := LinearOrder.lift' e e.injective
  obtain ⟨P, M, hdist, hdom, hP, hleft, hright⟩ :=
    PartialAmalgam.exists_partial_span (emptyForbiddenFamily n) (emptyForbiddenFamily_pairCancelling n)
      AA BB CC f g hAB hAC (omits_emptyForbiddenFamily BB) (omits_emptyForbiddenFamily CC)
  obtain ⟨D, hPD, _⟩ := exists_pair_cancelling_completion hn P M hdist hdom
    (emptyForbiddenFamily n) (emptyForbiddenFamily_pairCancelling n) hP
  exact ⟨D, fun t => hPD _ _ (hleft t), fun t => hPD _ _ (hright t)⟩

/-- Both supplied orders extend on the same literal unrestricted strong carrier. -/
theorem unrestricted_ordered_strong_span {n : ℕ} (hn : 2 ≤ n)
    {A : Type u} {B : Type v} {C : Type w} [Finite A] [Finite B] [Finite C]
    [LinearOrder A] [LinearOrder B] [LinearOrder C]
    (AA : Hyper n A) (BB : Hyper n B) (CC : Hyper n C)
    (f : A ↪o B) (g : A ↪o C)
    (hAB : Preserves AA BB f.toEmbedding) (hAC : Preserves AA CC g.toEmbedding) :
    ∃ (order : LinearOrder (FiniteStrongSpan.Carrier f.toEmbedding g.toEmbedding))
      (D : Hyper n (FiniteStrongSpan.Carrier f.toEmbedding g.toEmbedding)),
      Preserves BB D (FiniteStrongSpan.left f.toEmbedding g.toEmbedding) ∧
      Preserves CC D (FiniteStrongSpan.right f.toEmbedding g.toEmbedding) ∧
      (∀ x y : B, x < y → @LT.lt _ order.toLT
        (FiniteStrongSpan.left f.toEmbedding g.toEmbedding x)
        (FiniteStrongSpan.left f.toEmbedding g.toEmbedding y)) ∧
      (∀ x y : C, x < y → @LT.lt _ order.toLT
        (FiniteStrongSpan.right f.toEmbedding g.toEmbedding x)
        (FiniteStrongSpan.right f.toEmbedding g.toEmbedding y)) := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let : Fintype B := Fintype.ofFinite B
  let : Fintype C := Fintype.ofFinite C
  obtain ⟨order, hiOrder, hjOrder⟩ := OrderedStrongSpan.exists_order_on_carrier f g
  obtain ⟨D, hi, hj⟩ := unrestricted_strong_span hn AA BB CC
    f.toEmbedding g.toEmbedding hAB hAC
  exact ⟨order, D, hi, hj, hiOrder, hjOrder⟩

/-- The original finite-presentation SAP interface for the unrestricted class. -/
theorem unrestricted_hasStrongAmalgamation {n : ℕ} (hn : 2 ≤ n) :
    HasStrongAmalgamation (emptyForbiddenFamily n) := by
  classical
  intro a b c A B C _hA _hB _hC f g hf hg
  obtain ⟨D, hi, hj⟩ := unrestricted_strong_span hn A B C f g hf hg
  let e := Fintype.equivFin (FiniteStrongSpan.Carrier f g)
  let D' := D.pullback e.symm.toEmbedding
  let i := (FiniteStrongSpan.left f g).trans e.toEmbedding
  let j := (FiniteStrongSpan.right f g).trans e.toEmbedding
  refine ⟨Fintype.card (FiniteStrongSpan.Carrier f g), D', i, j,
    omits_emptyForbiddenFamily D', ?_, ?_, ?_, ?_⟩
  · intro t
    have ht : (t.trans i).trans e.symm.toEmbedding = t.trans (FiniteStrongSpan.left f g) := by
      ext k
      simp [i]
    change D.orient ((t.trans i).trans e.symm.toEmbedding) = _
    rw [ht]
    exact hi t
  · intro t
    have ht : (t.trans j).trans e.symm.toEmbedding = t.trans (FiniteStrongSpan.right f g) := by
      ext k
      simp [j]
    change D.orient ((t.trans j).trans e.symm.toEmbedding) = _
    rw [ht]
    exact hj t
  · intro x
    exact congrArg e (FiniteStrongSpan.commutes f g x)
  · intro y z heq
    exact (FiniteStrongSpan.overlap f g y z).mp (e.injective heq)

end Hypertournaments
