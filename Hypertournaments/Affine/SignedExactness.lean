import Hypertournaments.Affine.SignedContraction
import Hypertournaments.Affine.SignedPermutation
import Hypertournaments.Affine.LinearOperations
import Mathlib.Tactic.Abel

/-!
# Exactness and signed gauge differences on a full simplex

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`Further potential constructions`. A literal root contraction proves
exactness for ordinary alternating cochains over every abelian group.
The positive-degree statement includes empty carriers.
-/

universe u v

namespace Hypertournaments.Affine

variable {V : Type v} {G : Type u} [AddCommGroup G]

/-- Away from the root, the cone identity has its ordinary integral sign. -/
theorem signedCoboundary_cons {n : ℕ} (a : V)
    (c : (Fin (n + 1) ↪ V) → G) (f : Fin (n + 1) ↪ V)
    (ha : a ∉ Set.range f) :
    signedCoboundary c (Fin.Embedding.cons f ha) =
      c f - signedCoboundary (contractTuple a c) f := by
  classical
  have htail (i : Fin (n + 1)) :
      c (facet (Fin.Embedding.cons f ha) i.succ) = contractTuple a c (facet f i) := by
    have hn : a ∉ Set.range (facet f i) := by
      rintro ⟨j, hj⟩
      exact ha ⟨i.succAbove j, hj⟩
    rw [facet_cons_succ, contractTuple_of_not_mem a c _ hn]
  unfold signedCoboundary
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, facet_cons_zero, Fin.val_succ,
    pow_succ, mul_neg_one, neg_smul, htail, Finset.sum_neg_distrib]
  rw [sub_eq_add_neg]

/-- On a root-first tuple, the contraction recovers the original value directly. -/
theorem signedCoboundary_contractAt_root_first {n : ℕ} (a : V)
    (c : AlternatingCochain (n + 1) V G) (f : Fin (n + 1) ↪ V) (hf : f 0 = a) :
    signedCoboundary (Labelled.contractAt a c).label f = c.label f := by
  subst a
  change signedCoboundary (contractTuple (f 0) c.label) f = c.label f
  unfold signedCoboundary
  rw [Fin.sum_univ_succ]
  have hzero (i : Fin n) : contractTuple (f 0) c.label (facet f i.succ) = 0 :=
    contractTuple_of_mem _ _ _ (root_mem_facet_succ f i)
  simp only [Fin.val_zero, pow_zero, one_smul, hzero, smul_zero,
    Finset.sum_const_zero, add_zero]
  rw [contractTuple_of_not_mem _ _ _ (root_not_mem_facet_zero f), cons_facet_zero]

/-- The explicit cone is a potential for every closed ordinary alternating cochain. -/
theorem signedCoboundary_contractAt_of_closed {n : ℕ} (a : V)
    (c : AlternatingCochain (n + 1) V G)
    (hclosed : ∀ f : Fin (n + 2) ↪ V, signedCoboundary c.label f = 0)
    (f : Fin (n + 1) ↪ V) :
    signedCoboundary (Labelled.contractAt a c).label f = c.label f := by
  classical
  by_cases ha : a ∈ Set.range f
  · obtain ⟨i, hi⟩ := ha
    by_cases hi0 : i = 0
    · exact signedCoboundary_contractAt_root_first a c f (hi0 ▸ hi)
    · let f' := (Equiv.swap (0 : Fin (n + 1)) i).toEmbedding.trans f
      have hf' : f' 0 = a := by simpa [f'] using hi
      have h := signedCoboundary_contractAt_root_first a c f' hf'
      have hp := signedCoboundary_swap (Labelled.contractAt a c)
        (by intro _; rfl) f 0 i (Ne.symm hi0)
      have hc := c.swap_label f 0 i (Ne.symm hi0)
      change signedCoboundary (Labelled.contractAt a c).label
        ((Equiv.swap 0 i).toEmbedding.trans f) = _ at h
      rw [hp, hc] at h
      simpa only [Palette.affine_star, zero_sub, neg_inj] using h
  · have h := signedCoboundary_cons a c.label f ha
    rw [hclosed] at h
    exact (sub_eq_zero.mp h.symm).symm

/-- Full-simplex exactness in every positive degree, including empty carriers.
No finiteness, carrier order, or characteristic assumption is needed. -/
theorem exists_signed_potential {n : ℕ} (c : AlternatingCochain (n + 1) V G)
    (hclosed : ∀ f : Fin (n + 2) ↪ V, signedCoboundary c.label f = 0) :
    ∃ p : AlternatingCochain n V G,
      ∀ f : Fin (n + 1) ↪ V, signedCoboundary p.label f = c.label f := by
  classical
  by_cases hV : Nonempty V
  · let a := Classical.choice hV
    exact ⟨Labelled.contractAt a c, signedCoboundary_contractAt_of_closed a c hclosed⟩
  · refine ⟨Labelled.linearZero n G V, ?_⟩
    intro f
    exact (hV ⟨f 0⟩).elim

/-- Equal affine coboundaries differ by a genuinely signed lower gauge. -/
theorem exists_signed_gauge {n : ℕ} {a : G}
    (p q : Labelled (n + 1) (Palette.affine a) V)
    (heq : ∀ f : Fin (n + 2) ↪ V, signedCoboundary p.label f = signedCoboundary q.label f) :
    ∃ s : AlternatingCochain n V G, ∀ t : Fin (n + 1) ↪ V,
      p.label t = q.label t + signedCoboundary s.label t := by
  have hclosed : ∀ f : Fin (n + 2) ↪ V,
      signedCoboundary (p.affineSub q).label f = 0 := by
    intro f
    change signedCoboundary (fun t => p.label t - q.label t) f = 0
    rw [signedCoboundary_sub, heq, sub_self]
  obtain ⟨s, hs⟩ := exists_signed_potential (p.affineSub q) hclosed
  refine ⟨s, ?_⟩
  intro t
  rw [hs t]
  change p.label t = q.label t + (p.label t - q.label t)
  abel

end Hypertournaments.Affine
