import Hypertournaments.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Group.Subgroup.Actions
import Mathlib.Algebra.Group.Action.End
import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Intrinsic automorphisms and their pointwise stabilizers

Automorphisms are precisely the vertex permutations preserving the shared
intrinsic orientation. No auxiliary vertex order or relational presentation
is added. Pointwise stabilizers use the standard action of this actual
permutation subgroup on the vertex carrier.
-/

namespace Hypertournaments

universe u

/-- The actual orientation-preserving permutation subgroup. -/
def Hyper.automorphismGroup {n : ℕ} {V : Type u} (A : Hyper n V) :
    Subgroup (Equiv.Perm V) where
  carrier := {g | Preserves A A g.toEmbedding}
  one_mem' := by
    intro t
    rfl
  mul_mem' := by
    intro g h hg hh t
    exact (hg (t.trans h.toEmbedding)).trans (hh t)
  inv_mem' := by
    intro g hg t
    have ht : (t.trans g.symm.toEmbedding).trans g.toEmbedding = t := by
      ext i
      exact g.apply_symm_apply (t i)
    have h := hg (t.trans g.symm.toEmbedding)
    rw [ht] at h
    exact h.symm

@[simp] theorem Hyper.mem_automorphismGroup_iff {n : ℕ} {V : Type u}
    {A : Hyper n V} {g : Equiv.Perm V} :
    g ∈ A.automorphismGroup ↔ Preserves A A g.toEmbedding := Iff.rfl

/-- Intrinsic automorphisms, with the inherited group and faithful action. -/
abbrev Hyper.Aut {n : ℕ} {V : Type u} (A : Hyper n V) : Type u :=
  A.automorphismGroup

theorem Hyper.Aut.preserves {n : ℕ} {V : Type u} {A : Hyper n V} (g : A.Aut) :
    Preserves A A (g : Equiv.Perm V).toEmbedding := g.property

@[ext] theorem Hyper.Aut.ext {n : ℕ} {V : Type u} {A : Hyper n V}
    {g h : A.Aut} (he : ∀ x, (g : Equiv.Perm V) x = (h : Equiv.Perm V) x) : g = h :=
  Subtype.ext (Equiv.ext he)

@[simp] theorem Hyper.Aut.smul_def {n : ℕ} {V : Type u} {A : Hyper n V}
    (g : A.Aut) (x : V) : g • x = (g : Equiv.Perm V) x := rfl

instance Hyper.Aut.finite {n : ℕ} {V : Type u} [Finite V] (A : Hyper n V) :
    Finite A.Aut := by
  classical
  let : Fintype V := Fintype.ofFinite V
  infer_instance

/-- The subgroup of actual automorphisms fixing every vertex of a set. -/
def Hyper.pointwiseStabilizer {n : ℕ} {V : Type u}
    (A : Hyper n V) (S : Set V) : Subgroup A.Aut :=
  fixingSubgroup A.Aut S

@[simp] theorem Hyper.mem_pointwiseStabilizer_iff {n : ℕ} {V : Type u}
    {A : Hyper n V} {S : Set V} {g : A.Aut} :
    g ∈ A.pointwiseStabilizer S ↔ ∀ x ∈ S, (g : Equiv.Perm V) x = x :=
  mem_fixingSubgroup_iff A.Aut

end Hypertournaments
