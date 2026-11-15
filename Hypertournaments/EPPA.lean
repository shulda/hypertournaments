import Hypertournaments.Automorphism
import Hypertournaments.PartialHyper

/-!
# Ordinary finite EPPA for intrinsic hypertournaments

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`prop:higharity-eppa-obstruction`. Partial automorphisms are isomorphisms
between actual induced subsets. Each one extends separately; no coherent
choice of extensions is required. Witnesses have finite entire carriers.
-/

universe u v w

namespace Hypertournaments

/-- The literal inclusion of a vertex subset. -/
def subsetEmbedding {V : Type u} (S : Set V) : S ↪ V :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-- A partial automorphism is an intrinsic induced isomorphism of subsets. -/
structure Hyper.PartialAutomorphism {n : ℕ} {V : Type u} (A : Hyper n V) where
  source : Set V
  target : Set V
  equiv : source ≃ target
  preserves : Preserves (A.pullback (subsetEmbedding source))
    (A.pullback (subsetEmbedding target)) equiv.toEmbedding

def Hyper.PartialAutomorphism.identity {n : ℕ} {V : Type u}
    (A : Hyper n V) (S : Set V) : A.PartialAutomorphism where
  source := S
  target := S
  equiv := Equiv.refl S
  preserves _ := rfl

/-- Finite EPPA witnesses use the original orientation-preserving embedding
and the actual full automorphism group of the extension. -/
structure Hyper.IsEPPAWitness {n : ℕ} {V : Type u} {W : Type v}
    (A : Hyper n V) (B : Hyper n W) (e : V ↪ W) : Prop where
  finite : Finite W
  preserves : Preserves A B e
  extension : ∀ p : A.PartialAutomorphism, ∃ g : B.Aut,
    ∀ x : p.source, (g : Equiv.Perm W) (e x) = e (p.equiv x)

/-- Reindex an actual automorphism without changing its orientation law. -/
def Hyper.Aut.reindex {n : ℕ} {V : Type u} {W : Type v}
    {A : Hyper n V} (g : A.Aut) (s : V ≃ W) :
    (A.pullback s.symm.toEmbedding).Aut := by
  let h : Equiv.Perm W := (s.symm.trans (g : Equiv.Perm V)).trans s
  refine ⟨h, ?_⟩
  intro t
  have ht : (t.trans h.toEmbedding).trans s.symm.toEmbedding =
      (t.trans s.symm.toEmbedding).trans (g : Equiv.Perm V).toEmbedding := by
    ext i
    exact s.symm_apply_apply _
  change A.orient ((t.trans h.toEmbedding).trans s.symm.toEmbedding) = _
  rw [ht]
  exact g.preserves (t.trans s.symm.toEmbedding)

@[simp] theorem Hyper.Aut.reindex_apply {n : ℕ} {V : Type u} {W : Type v}
    {A : Hyper n V} (g : A.Aut) (s : V ≃ W) (x : W) :
    ((g.reindex s : (A.pullback s.symm.toEmbedding).Aut) : Equiv.Perm W) x =
      s ((g : Equiv.Perm V) (s.symm x)) := rfl

/-- A finite witness is independent of the chosen presentation of its carrier. -/
theorem Hyper.IsEPPAWitness.reindex {n : ℕ} {V : Type u} {W : Type v} {X : Type w}
    {A : Hyper n V} {B : Hyper n W} {e : V ↪ W}
    (h : A.IsEPPAWitness B e) (s : W ≃ X) :
    A.IsEPPAWitness (B.pullback s.symm.toEmbedding) (e.trans s.toEmbedding) := by
  let : Finite W := h.finite
  refine ⟨Finite.of_injective s.symm s.symm.injective, ?_, ?_⟩
  · intro t
    have ht : (t.trans (e.trans s.toEmbedding)).trans s.symm.toEmbedding = t.trans e := by
      ext i
      exact s.symm_apply_apply _
    change B.orient ((t.trans (e.trans s.toEmbedding)).trans s.symm.toEmbedding) = _
    rw [ht]
    exact h.preserves t
  · intro p
    obtain ⟨g, hg⟩ := h.extension p
    refine ⟨g.reindex s, ?_⟩
    intro x
    change s ((g : Equiv.Perm W) (s.symm (s (e x)))) = s (e (p.equiv x))
    rw [s.symm_apply_apply, hg x]

/-- Unrestricted finite EPPA witnesses, presented on finite ordinals. -/
def Hyper.HasFiniteEPPAWitness {n : ℕ} {V : Type u} (A : Hyper n V) : Prop :=
  ∃ (m : ℕ) (B : Hyper n (Fin m)) (e : V ↪ Fin m), A.IsEPPAWitness B e

/-- Every actual finite-carrier witness gives the finite-ordinal interface. -/
theorem Hyper.IsEPPAWitness.hasFiniteEPPAWitness
    {n : ℕ} {V : Type u} {W : Type v}
    {A : Hyper n V} {B : Hyper n W} {e : V ↪ W} (h : A.IsEPPAWitness B e) :
    A.HasFiniteEPPAWitness := by
  classical
  let : Finite W := h.finite
  let : Fintype W := Fintype.ofFinite W
  exact ⟨_, _, _, h.reindex (Fintype.equivFin W)⟩

/-- Ordinary EPPA within the specified omission class. -/
def HasEPPA {n : ℕ} (family : ForbiddenFamily n) : Prop :=
  ∀ (a : ℕ) (A : Hyper n (Fin a)), Omits family A →
    ∃ (b : ℕ) (B : Hyper n (Fin b)) (e : Fin a ↪ Fin b),
      Omits family B ∧ A.IsEPPAWitness B e

/-- A single obstruction to unrestricted finite witnesses excludes EPPA
in every omission class containing that structure. -/
theorem not_hasEPPA_of_unrestricted_obstruction {n a : ℕ}
    (family : ForbiddenFamily n) (A : Hyper n (Fin a))
    (hA : Omits family A) (hbad : ¬ A.HasFiniteEPPAWitness) : ¬ HasEPPA family := by
  intro h
  obtain ⟨b, B, e, _, hw⟩ := h a A hA
  exact hbad ⟨b, B, e, hw⟩

end Hypertournaments
