import Hypertournaments.Affine.SignedExactness
import Hypertournaments.Affine.PotentialBasics
import Mathlib.Tactic.Ext

/-!
# Relative alignment by signed gauges

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`Further potential constructions`. Ordinary lower alternating gauges
extend by zero along arbitrary injections. Their coboundaries align
an existing potential with any prescribed potential on an induced base.
-/

universe u v w z

namespace Hypertournaments.Affine

variable {G : Type u} [AddCommGroup G]

/-- Pull an injective tuple back through its actual containment in an image. -/
noncomputable def tuplePreimage {n : ℕ} {A : Type v} {C : Type w}
    (e : A ↪ C) (t : Fin n ↪ C) (h : ∀ i, t i ∈ Set.range e) : Fin n ↪ A where
  toFun i := Classical.choose (h i)
  inj' i j hij := by
    apply t.injective
    calc
      t i = e (Classical.choose (h i)) := (Classical.choose_spec (h i)).symm
      _ = e (Classical.choose (h j)) := congrArg e hij
      _ = t j := Classical.choose_spec (h j)

@[simp] theorem tuplePreimage_trans {n : ℕ} {A : Type v} {C : Type w}
    (e : A ↪ C) (t : Fin n ↪ C) (h : ∀ i, t i ∈ Set.range e) :
    (tuplePreimage e t h).trans e = t := by
  ext i
  exact Classical.choose_spec (h i)

theorem tuplePreimage_image {n : ℕ} {A : Type v} {C : Type w}
    (e : A ↪ C) (t : Fin n ↪ A) (h : ∀ i, (t.trans e) i ∈ Set.range e) :
    tuplePreimage e (t.trans e) h = t := by
  ext i
  apply e.injective
  exact Classical.choose_spec (h i)

theorem tuplePreimage_swap {n : ℕ} {A : Type v} {C : Type w}
    (e : A ↪ C) (t : Fin n ↪ C) (i j : Fin n)
    (h : ∀ k, t k ∈ Set.range e)
    (h' : ∀ k, ((Equiv.swap i j).toEmbedding.trans t) k ∈ Set.range e) :
    tuplePreimage e ((Equiv.swap i j).toEmbedding.trans t) h' =
      (Equiv.swap i j).toEmbedding.trans (tuplePreimage e t h) := by
  ext k
  apply e.injective
  exact (Classical.choose_spec (h' k)).trans (Classical.choose_spec (h (Equiv.swap i j k))).symm

/-- Extend an ordinary signed cochain by zero outside the vertex image. -/
noncomputable def Labelled.extendLinear {n : ℕ} {A : Type v} {C : Type w}
    (e : A ↪ C) (s : AlternatingCochain n A G) : AlternatingCochain n C G where
  label t := by
    classical
    exact if h : ∀ i, t i ∈ Set.range e then s.label (tuplePreimage e t h) else 0
  swap_label t i j hij := by
    classical
    have hiff : (∀ k, ((Equiv.swap i j).toEmbedding.trans t) k ∈ Set.range e) ↔
        ∀ k, t k ∈ Set.range e := by
      constructor
      · intro h k
        simpa using h (Equiv.swap i j k)
      · intro h k
        exact h (Equiv.swap i j k)
    by_cases h : ∀ k, t k ∈ Set.range e
    · rw [dite_eq_left h, dite_eq_left (hiff.mpr h), tuplePreimage_swap,
        s.swap_label _ _ _ hij]
    · rw [dite_eq_right h, dite_eq_right (fun h' => h (hiff.mp h'))]
      simp

@[simp] theorem Labelled.extendLinear_label_trans {n : ℕ} {A : Type v} {C : Type w}
    (e : A ↪ C) (s : AlternatingCochain n A G) (t : Fin n ↪ A) :
    (Labelled.extendLinear e s).label (t.trans e) = s.label t := by
  classical
  have h : ∀ i, (t.trans e) i ∈ Set.range e := fun i => ⟨t i, rfl⟩
  change (if h' : ∀ i, (t.trans e) i ∈ Set.range e then
    s.label (tuplePreimage e (t.trans e) h') else 0) = _
  rw [dite_eq_left h, tuplePreimage_image]

theorem Labelled.extendLinear_label_of_outside {n : ℕ} {A : Type v} {C : Type w}
    (e : A ↪ C) (s : AlternatingCochain n A G) (t : Fin n ↪ C)
    (h : ∃ i, t i ∉ Set.range e) : (Labelled.extendLinear e s).label t = 0 := by
  classical
  obtain ⟨i, hi⟩ := h
  have hn : ¬ ∀ j, t j ∈ Set.range e := fun h' => hi (h' i)
  exact dite_eq_right hn

theorem Labelled.extendLinear_preserves {n : ℕ} {A : Type v} {C : Type w}
    (e : A ↪ C) (s : AlternatingCochain n A G) : s.Preserves (Labelled.extendLinear e s) e :=
  Labelled.extendLinear_label_trans e s

/-- The extended signed gauge has its original coboundary on every source tuple. -/
theorem signedCoboundary_extendLinear_trans {n : ℕ} {A : Type v} {C : Type w}
    (e : A ↪ C) (s : AlternatingCochain n A G) (t : Fin (n + 1) ↪ A) :
    signedCoboundary (Labelled.extendLinear e s).label (t.trans e) =
      signedCoboundary s.label t := by
  unfold signedCoboundary
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun x : G => (-1 : ℤ) ^ i.val • x)
    (Labelled.extendLinear_label_trans e s (facet t i))

/-- Adding an exact ordinary alternating term retains the same raw potential equation. -/
theorem IsPotential.affineAddLinear_coboundary {n : ℕ} {Q : Type v} {d : Data Q G}
    {C : Type w} {raw : Labelled (n + 2) d.palette C}
    {p : Labelled (n + 1) (Palette.affine d.offset) C}
    (hp : IsPotential d raw p) (s : AlternatingCochain n C G) :
    IsPotential d raw (p.affineAddLinear (s.coboundary (by intro _; rfl))) := by
  intro t
  change signedCoboundary (fun f => p.label f + signedCoboundary s.label f) t = _
  rw [signedCoboundary_add, signedCoboundary_signedCoboundary_zero, add_zero]
  exact hp t

/-- A prescribed positive-degree potential on an induced base can be aligned
with the ambient potential, retaining every original vertex and label. -/
theorem IsPotential.exists_aligned_succ {n : ℕ} {Q : Type v} {d : Data Q G}
    {A : Type w} {C : Type z} {raw : Labelled (n + 2) d.palette C}
    {pC : Labelled (n + 1) (Palette.affine d.offset) C}
    (hC : IsPotential d raw pC) (pA : Labelled (n + 1) (Palette.affine d.offset) A)
    (g : A ↪ C) (hA : IsPotential d (raw.pullback g) pA) :
    ∃ pC' : Labelled (n + 1) (Palette.affine d.offset) C,
      IsPotential d raw pC' ∧ pA.Preserves pC' g := by
  have heq (t : Fin (n + 2) ↪ A) :
      signedCoboundary pA.label t = signedCoboundary (pC.pullback g).label t :=
    (hA t).trans ((hC.pullback g) t).symm
  obtain ⟨s, hs⟩ := exists_signed_gauge pA (pC.pullback g) heq
  let extended := Labelled.extendLinear g s
  refine ⟨pC.affineAddLinear (extended.coboundary (by intro _; rfl)),
    hC.affineAddLinear_coboundary extended, ?_⟩
  intro t
  change pC.label (t.trans g) + signedCoboundary extended.label (t.trans g) = pA.label t
  rw [signedCoboundary_extendLinear_trans g s t]
  exact (hs t).symm

/-- Empty-base-safe relative extension in every positive potential degree. -/
theorem IsPotential.exists_aligned {r : ℕ} {Q : Type v} {d : Data Q G}
    {A : Type w} {C : Type z} {raw : Labelled (r + 1) d.palette C}
    {pC : Labelled r (Palette.affine d.offset) C}
    (hC : IsPotential d raw pC) (pA : Labelled r (Palette.affine d.offset) A)
    (g : A ↪ C) (hA : IsPotential d (raw.pullback g) pA) (hr : 0 < r) :
    ∃ pC' : Labelled r (Palette.affine d.offset) C,
      IsPotential d raw pC' ∧ pA.Preserves pC' g := by
  cases r with
  | zero => exact (Nat.lt_irrefl 0 hr).elim
  | succ n => exact hC.exists_aligned_succ pA g hA

end Hypertournaments.Affine
