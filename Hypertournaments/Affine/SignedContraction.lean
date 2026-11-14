import Hypertournaments.Affine.Basic
import Hypertournaments.LocalTypes
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Tactic.Ext

/-!
# Root contraction of ordinary alternating cochains

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`Further potential constructions`. The root is prepended when absent,
and the contracted value is zero when the root is already present.
-/

universe u v

namespace Hypertournaments.Affine

variable {V : Type v} {G : Type u} [AddCommGroup G]

/-- The tuple-level cone contraction at a root. -/
noncomputable def contractTuple {n : ℕ} (a : V)
    (c : (Fin (n + 1) ↪ V) → G) (t : Fin n ↪ V) : G := by
  classical
  exact if h : a ∈ Set.range t then 0 else c (Fin.Embedding.cons t h)

theorem contractTuple_of_mem {n : ℕ} (a : V) (c : (Fin (n + 1) ↪ V) → G)
    (t : Fin n ↪ V) (h : a ∈ Set.range t) : contractTuple a c t = 0 := by
  classical
  simp only [contractTuple, dite_eq_left h]

theorem contractTuple_of_not_mem {n : ℕ} (a : V) (c : (Fin (n + 1) ↪ V) → G)
    (t : Fin n ↪ V) (h : a ∉ Set.range t) :
    contractTuple a c t = c (Fin.Embedding.cons t h) := by
  classical
  simp only [contractTuple, dite_eq_right h]

theorem facet_cons_zero {n : ℕ} (t : Fin n ↪ V) {a : V} (ha : a ∉ Set.range t) :
    facet (Fin.Embedding.cons t ha) 0 = t := by
  ext i
  simp [facet]

theorem facet_cons_succ {n : ℕ} (t : Fin (n + 1) ↪ V) {a : V}
    (ha : a ∉ Set.range t) (i : Fin (n + 1)) :
    facet (Fin.Embedding.cons t ha) i.succ =
      Fin.Embedding.cons (facet t i) (by
        rintro ⟨j, hj⟩
        exact ha ⟨i.succAbove j, hj⟩) := by
  ext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [facet]
  · simp [facet]

theorem root_not_mem_facet_zero {n : ℕ} (f : Fin (n + 1) ↪ V) :
    f 0 ∉ Set.range (facet f 0) := by
  rintro ⟨i, hi⟩
  have h : (0 : Fin (n + 1)) = i.succ := by
    apply f.injective
    simpa [facet] using hi.symm
  exact Fin.succ_ne_zero i h.symm

theorem cons_facet_zero {n : ℕ} (f : Fin (n + 1) ↪ V) :
    Fin.Embedding.cons (facet f 0) (root_not_mem_facet_zero f) = f := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp [facet]

theorem root_mem_facet_succ {n : ℕ} (f : Fin (n + 1) ↪ V) (i : Fin n) :
    f 0 ∈ Set.range (facet f i.succ) := by
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (Ne.symm (Fin.succ_ne_zero i))
  exact ⟨k, congrArg f hk⟩

theorem contractTuple_swap {n : ℕ} (a : V)
    (c : Labelled (n + 1) (Palette.affine (0 : G)) V)
    (t : Fin n ↪ V) (i j : Fin n) (hij : i ≠ j) :
    contractTuple a c.label ((Equiv.swap i j).toEmbedding.trans t) =
      - contractTuple a c.label t := by
  classical
  have hmem : a ∈ Set.range ((Equiv.swap i j).toEmbedding.trans t) ↔ a ∈ Set.range t := by
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨Equiv.swap i j k, hk⟩
    · rintro ⟨k, hk⟩
      exact ⟨Equiv.swap i j k, by simpa using hk⟩
  by_cases ha : a ∈ Set.range t
  · rw [contractTuple_of_mem a c.label _ (hmem.mpr ha), contractTuple_of_mem a c.label _ ha]
    exact neg_zero.symm
  · have ha' : a ∉ Set.range ((Equiv.swap i j).toEmbedding.trans t) :=
      fun h => ha (hmem.mp h)
    rw [contractTuple_of_not_mem a c.label _ ha', contractTuple_of_not_mem a c.label _ ha]
    have hcons : Fin.Embedding.cons ((Equiv.swap i j).toEmbedding.trans t) ha' =
        (Equiv.swap i.succ j.succ).toEmbedding.trans (Fin.Embedding.cons t ha) := by
      ext k
      refine Fin.cases ?_ (fun k => ?_) k
      · simp [Equiv.swap_apply_def, Ne.symm (Fin.succ_ne_zero i),
          Ne.symm (Fin.succ_ne_zero j)]
      · by_cases hki : k = i <;> by_cases hkj : k = j <;>
          simp [Equiv.swap_apply_def, hki, hkj]
    rw [hcons, c.swap_label _ _ _ (by exact fun h => hij (Fin.succ_injective _ h))]
    simp

/-- Root contraction retains the ordinary alternating law over any abelian group. -/
noncomputable def Labelled.contractAt {n : ℕ} (a : V)
    (c : Labelled (n + 1) (Palette.affine (0 : G)) V) :
    Labelled n (Palette.affine (0 : G)) V where
  label := contractTuple a c.label
  swap_label t i j hij := by
    simpa only [Palette.affine_star, zero_sub] using contractTuple_swap a c t i j hij

end Hypertournaments.Affine
