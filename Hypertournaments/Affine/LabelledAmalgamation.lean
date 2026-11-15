import Hypertournaments.Affine.OrderedLabels
import Hypertournaments.FiniteStrongSpan
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Choose
import Mathlib.Tactic.SplitIfs

/-!
# Free strong amalgamation of involution-labelled structures

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`Further potential constructions`. A canonical table glues the two original
copies on an exact-overlap carrier and gives mixed subsets any fixed label.
-/

universe u v w z s

namespace Hypertournaments.Affine

private theorem tupleVertices_card {n : ℕ} {X : Type s} [DecidableEq X]
    (t : Fin n ↪ X) : (tupleVertices t).card = n := by
  unfold tupleVertices
  rw [Finset.card_image_of_injective _ t.injective]
  exact Finset.card_fin n

private theorem canonical_tuple_eq {n : ℕ} {X : Type s} [LinearOrder X]
    (t : Fin n ↪ X) (ht : StrictMono (t : Fin n → X)) :
    ((tupleVertices t).orderEmbOfFin (tupleVertices_card t)).toEmbedding = t := by
  ext k
  exact (congrFun (Finset.orderEmbOfFin_unique (tupleVertices_card t)
    (fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)) ht) k).symm

private noncomputable def amalgamTable {n : ℕ} {Q : Type u} {P : Palette Q}
    {B : Type w} {C : Type z} {X : Type s} [LinearOrder X]
    (BB : Labelled n P B) (CC : Labelled n P C) (i : B ↪ X) (j : C ↪ X)
    (fallback : Q) (S : Finset X) : Q := by
  classical
  exact if hS : S.card = n then
    if hi : ∃ t : Fin n ↪ B, t.trans i = (S.orderEmbOfFin hS).toEmbedding then
      BB.label (Classical.choose hi)
    else if hj : ∃ t : Fin n ↪ C, t.trans j = (S.orderEmbOfFin hS).toEmbedding then
      CC.label (Classical.choose hj)
    else fallback
  else fallback

private theorem amalgamTable_left {n : ℕ} {Q : Type u} {P : Palette Q}
    {B : Type w} {C : Type z} {X : Type s} [LinearOrder X]
    (BB : Labelled n P B) (CC : Labelled n P C) (i : B ↪ X) (j : C ↪ X)
    (fallback : Q) (t : Fin n ↪ B) (ht : StrictMono (t.trans i : Fin n → X)) :
    amalgamTable BB CC i j fallback (tupleVertices (t.trans i)) = BB.label t := by
  classical
  have he := canonical_tuple_eq (t.trans i) ht
  have hi : ∃ s : Fin n ↪ B, s.trans i =
      ((tupleVertices (t.trans i)).orderEmbOfFin (tupleVertices_card _)).toEmbedding :=
    ⟨t, he.symm⟩
  rw [amalgamTable, dite_eq_left (tupleVertices_card _), dite_eq_left hi]
  have hs : Classical.choose hi = t := by
    ext k
    apply i.injective
    exact congrArg (fun s : Fin n ↪ X => s k) ((Classical.choose_spec hi).trans he)
  rw [hs]

private theorem amalgamTable_right {n : ℕ} {Q : Type u} {P : Palette Q}
    {B : Type w} {C : Type z} {X : Type s} [LinearOrder X]
    (BB : Labelled n P B) (CC : Labelled n P C) (i : B ↪ X) (j : C ↪ X)
    (fallback : Q)
    (hagree : ∀ (t : Fin n ↪ B) (s : Fin n ↪ C), t.trans i = s.trans j → BB.label t = CC.label s)
    (t : Fin n ↪ C) (ht : StrictMono (t.trans j : Fin n → X)) :
    amalgamTable BB CC i j fallback (tupleVertices (t.trans j)) = CC.label t := by
  classical
  have he := canonical_tuple_eq (t.trans j) ht
  have hj : ∃ s : Fin n ↪ C, s.trans j =
      ((tupleVertices (t.trans j)).orderEmbOfFin (tupleVertices_card _)).toEmbedding :=
    ⟨t, he.symm⟩
  rw [amalgamTable, dite_eq_left (tupleVertices_card _)]
  split_ifs with hi
  · exact hagree (Classical.choose hi) t ((Classical.choose_spec hi).trans he)
  · have hs : Classical.choose hj = t := by
      ext k
      apply j.injective
      exact congrArg (fun s : Fin n ↪ X => s k) ((Classical.choose_spec hj).trans he)
    rw [hs]

/-- Agreement on the actual overlap is the only constraint for a free amalgam. -/
theorem labelled_amalgam_on {n : ℕ} {Q : Type u} {P : Palette Q}
    {B : Type w} {C : Type z} {X : Type s} [LinearOrder X]
    (BB : Labelled n P B) (CC : Labelled n P C) (i : B ↪ X) (j : C ↪ X)
    (fallback : Q)
    (hagree : ∀ (t : Fin n ↪ B) (s : Fin n ↪ C), t.trans i = s.trans j → BB.label t = CC.label s) :
    ∃ D : Labelled n P X, BB.Preserves D i ∧ CC.Preserves D j := by
  classical
  let : LinearOrder B := LinearOrder.lift' i i.injective
  let : LinearOrder C := LinearOrder.lift' j j.injective
  let D : Labelled n P X := Labelled.fromOrderedLabels P (amalgamTable BB CC i j fallback)
  refine ⟨D, ?_, ?_⟩
  · apply Labelled.preserves_of_canonical
    intro S hS
    have ht : StrictMono (((S.orderEmbOfFin hS).toEmbedding.trans i : Fin n ↪ X) : Fin n → X) :=
      (S.orderEmbOfFin hS).strictMono
    rw [show D.label _ = _ from fromOrderedLabels_label_strictMono P _ _ ht]
    exact amalgamTable_left BB CC i j fallback _ ht
  · apply Labelled.preserves_of_canonical
    intro S hS
    have ht : StrictMono (((S.orderEmbOfFin hS).toEmbedding.trans j : Fin n ↪ X) : Fin n → X) :=
      (S.orderEmbOfFin hS).strictMono
    rw [show D.label _ = _ from fromOrderedLabels_label_strictMono P _ _ ht]
    exact amalgamTable_right BB CC i j fallback hagree _ ht

/-- Finite free strong amalgamation retains the original arbitrary injections,
including empty bases, empty sides, and arity zero. -/
theorem labelled_strong_span {n : ℕ} {Q : Type u} {P : Palette Q} [Nonempty Q]
    {A : Type v} {B : Type w} {C : Type z} [Finite B] [Finite C]
    (AA : Labelled n P A) (BB : Labelled n P B) (CC : Labelled n P C)
    (f : A ↪ B) (g : A ↪ C) (hAB : AA.Preserves BB f) (hAC : AA.Preserves CC g) :
    ∃ D : Labelled n P (FiniteStrongSpan.Carrier f g),
      BB.Preserves D (FiniteStrongSpan.left f g) ∧
      CC.Preserves D (FiniteStrongSpan.right f g) := by
  classical
  let X := FiniteStrongSpan.Carrier f g
  let i := FiniteStrongSpan.left f g
  let j := FiniteStrongSpan.right f g
  let : Fintype X := Fintype.ofFinite X
  let : LinearOrder X := LinearOrder.lift' (Fintype.equivFin X) (Fintype.equivFin X).injective
  apply labelled_amalgam_on BB CC i j (Classical.choice inferInstance)
  intro t s he
  have hx (k : Fin n) : ∃ a : A, f a = t k ∧ g a = s k :=
    (FiniteStrongSpan.overlap f g (t k) (s k)).mp
      (congrArg (fun h : Fin n ↪ X => h k) he)
  choose a ha hb using hx
  let u : Fin n ↪ A := ⟨a, fun k l h => t.injective ((ha k).symm.trans
    ((congrArg f h).trans (ha l)))⟩
  have huf : u.trans f = t := by ext k; exact ha k
  have hug : u.trans g = s := by ext k; exact hb k
  have hf := hAB u
  have hg := hAC u
  rw [huf] at hf
  rw [hug] at hg
  exact hf.trans hg.symm

end Hypertournaments.Affine
