import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Embedding.Basic
import Mathlib.Basic.Finite.Sum

/-!
# A finite carrier with exact overlap for a span of injections

The carrier is the left side together with the points of the right side
outside the common base. No quotient or nonempty-base assumption is used.
-/

universe u v w

namespace Hypertournaments.FiniteStrongSpan

variable {A : Type u} {B : Type v} {C : Type w}

abbrev Carrier (_f : A ↪ B) (g : A ↪ C) :=
  B ⊕ {c : C // c ∉ Set.range g}

instance finiteCarrier [Finite B] [Finite C] (f : A ↪ B) (g : A ↪ C) :
    Finite (Carrier f g) := by
  dsimp [Carrier]
  infer_instance

noncomputable instance fintypeCarrier [Fintype B] [Fintype C]
    (f : A ↪ B) (g : A ↪ C) : Fintype (Carrier f g) := by
  classical
  dsimp [Carrier]
  infer_instance

noncomputable def split (g : A ↪ C) :
    C ≃ A ⊕ {c : C // c ∉ Set.range g} := by
  classical
  exact (Equiv.Set.sumCompl (Set.range g)).symm.trans
    (Equiv.sumCongr (Equiv.ofInjective g g.injective).symm (Equiv.refl _))

@[simp] theorem split_base (g : A ↪ C) (a : A) :
    split g (g a) = Sum.inl a := by
  classical
  simp only [split, Equiv.trans_apply]
  rw [Equiv.Set.sumCompl_symm_apply_of_mem
    (show g a ∈ Set.range g from ⟨a, rfl⟩)]
  simp

@[simp] theorem split_new (g : A ↪ C)
    (c : {c : C // c ∉ Set.range g}) : split g c = Sum.inr c := by
  classical
  simp only [split, Equiv.trans_apply]
  rw [Equiv.Set.sumCompl_symm_apply_of_notMem c.property]
  rfl

def left (f : A ↪ B) (g : A ↪ C) : B ↪ Carrier f g :=
  Function.Embedding.inl

noncomputable def right (f : A ↪ B) (g : A ↪ C) : C ↪ Carrier f g :=
  (split g).toEmbedding.trans (f.sumMap (Function.Embedding.refl _))

@[simp] theorem right_base (f : A ↪ B) (g : A ↪ C) (a : A) :
    right f g (g a) = left f g (f a) := by
  change Sum.map f id (split g (g a)) = _
  rw [split_base]
  rfl

theorem commutes (f : A ↪ B) (g : A ↪ C) (a : A) :
    left f g (f a) = right f g (g a) :=
  (right_base f g a).symm

theorem overlap (f : A ↪ B) (g : A ↪ C) (b : B) (c : C) :
    left f g b = right f g c ↔ ∃ a, f a = b ∧ g a = c := by
  constructor
  · intro h
    cases hs : split g c with
    | inl a =>
      have hb : f a = b := by
        change Sum.inl b = Sum.map f id (split g c) at h
        simpa [hs] using h.symm
      have hc : g a = c := (split g).injective (by rw [split_base, hs])
      exact ⟨a, hb, hc⟩
    | inr z =>
      change Sum.inl b = Sum.map f id (split g c) at h
      simp [hs] at h
  · rintro ⟨a, rfl, rfl⟩
    exact commutes f g a

theorem covers (f : A ↪ B) (g : A ↪ C) (d : Carrier f g) :
    (∃ b, left f g b = d) ∨ (∃ c, right f g c = d) := by
  cases d with
  | inl b => exact Or.inl ⟨b, rfl⟩
  | inr c =>
    right
    refine ⟨c.val, ?_⟩
    change Sum.map f id (split g c.val) = _
    rw [split_new g c]
    rfl

end Hypertournaments.FiniteStrongSpan
