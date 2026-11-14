import Hypertournaments.EPPA
import Mathlib.Tactic.Ext

/-!
# Ordinary EPPA extends isomorphisms between embedded copies

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`prop:higharity-eppa-obstruction` and `prop:even-eppa-transfer`.
The source and target subsets are the literal ranges of the two injections.
-/

universe u v w

namespace Hypertournaments

theorem Preserves.comp {n : ℕ} {U : Type u} {V : Type v} {W : Type w}
    {P : Hyper n U} {A : Hyper n V} {B : Hyper n W} {f : U ↪ V} {e : V ↪ W}
    (he : Preserves A B e) (hf : Preserves P A f) : Preserves P B (f.trans e) := by
  intro t
  exact (he (t.trans f)).trans (hf t)

/-- The actual induced isomorphism between two copies of one structure. -/
noncomputable def Hyper.PartialAutomorphism.betweenCopies
    {n : ℕ} {U : Type u} {V : Type v} (P : Hyper n U) (A : Hyper n V)
    (f g : U ↪ V) (hf : Preserves P A f) (hg : Preserves P A g) :
    A.PartialAutomorphism where
  source := Set.range f
  target := Set.range g
  equiv := (Equiv.ofInjective f f.injective).symm.trans (Equiv.ofInjective g g.injective)
  preserves := by
    intro t
    let s := t.trans (Equiv.ofInjective f f.injective).symm.toEmbedding
    have hleft :
        (t.trans ((Equiv.ofInjective f f.injective).symm.trans
          (Equiv.ofInjective g g.injective)).toEmbedding).trans
            (subsetEmbedding (Set.range g)) = s.trans g := by
      ext i
      rfl
    have hright : t.trans (subsetEmbedding (Set.range f)) = s.trans f := by
      ext i
      exact (congrArg Subtype.val
        ((Equiv.ofInjective f f.injective).apply_symm_apply (t i))).symm
    change A.orient _ = A.orient _
    rw [hleft, hright]
    exact (hg s).trans (hf s).symm

@[simp] theorem Hyper.PartialAutomorphism.betweenCopies_equiv_apply
    {n : ℕ} {U : Type u} {V : Type v} (P : Hyper n U) (A : Hyper n V)
    (f g : U ↪ V) (hf : Preserves P A f) (hg : Preserves P A g) (x : U) :
    ((Hyper.PartialAutomorphism.betweenCopies P A f g hf hg).equiv
      ⟨f x, ⟨x, rfl⟩⟩ : V) = g x := by
  change ((Equiv.ofInjective g g.injective)
    ((Equiv.ofInjective f f.injective).symm
      ((Equiv.ofInjective f f.injective) x)) : V) = g x
  rw [Equiv.symm_apply_apply]
  rfl

/-- Ordinary separate extension of the induced isomorphism between any two
embedded copies. No coherent choice of automorphisms is imposed. -/
theorem Hyper.IsEPPAWitness.extend_isomorphism
    {n : ℕ} {U : Type u} {V : Type v} {W : Type w}
    {A : Hyper n V} {B : Hyper n W} {e : V ↪ W}
    (h : A.IsEPPAWitness B e) (P : Hyper n U) (f g : U ↪ V)
    (hf : Preserves P A f) (hg : Preserves P A g) :
    ∃ σ : B.Aut, ∀ x : U, (σ : Equiv.Perm W) (e (f x)) = e (g x) := by
  obtain ⟨σ, hσ⟩ := h.extension (Hyper.PartialAutomorphism.betweenCopies P A f g hf hg)
  refine ⟨σ, ?_⟩
  intro x
  simpa only [Hyper.PartialAutomorphism.betweenCopies_equiv_apply] using
    hσ ⟨f x, ⟨x, rfl⟩⟩

end Hypertournaments
