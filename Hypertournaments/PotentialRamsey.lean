import Hypertournaments.PotentialLanguage
import Hypertournaments.UnrestrictedRamsey

/-!
# Ramsey theorem for even hypertournaments with potentials

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`thm:potential` (Ramsey assertion). The full expanded language retains
both orientations and their freely chosen vertex order. Its embeddings
correspond exactly to embeddings of ordered lower-arity hypertournaments.
-/

universe v w

namespace Hypertournaments.Ramsey

open StructuralRamsey
open StructuralRamsey.Structure

/-- Actual potential expansions, finite on the whole carrier. -/
def potentialExpansionClass {r : ℕ} {V : Type v}
    (C : Structure (orderedPotentialLanguage r) V) : Prop :=
  Finite V ∧ ∃ (A : Hyper (r + 1) V) (φ : Hyper r V) (order : LinearOrder V),
    IsPotential A φ ∧ C = toOrderedPotential A φ order

/-- A finite full expanded Ramsey witness. All three named relations are
preserved and reflected by its Ramsey embeddings. -/
theorem exists_potential_ramsey_witness {r : ℕ} (hr : Even r) (hr2 : 2 ≤ r)
    {V W : Type v} [Finite V] [Finite W]
    (A : Hyper (r + 1) V) (B : Hyper (r + 1) W)
    (φ : Hyper r V) (ψ : Hyper r W) (hA : IsPotential A φ) (hB : IsPotential B ψ)
    (orderA : LinearOrder V) (orderB : LinearOrder W)
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    ∃ (X : Type v) (_ : Finite X) (D : Hyper (r + 1) X) (θ : Hyper r X)
      (order : LinearOrder X), IsPotential D θ ∧ D.IsEven ∧
      Structure.Arrow (toOrderedPotential A φ orderA) (toOrderedPotential B ψ orderB)
        (toOrderedPotential D θ order) κ := by
  obtain ⟨X, hX, θ, order, _, arrow⟩ :=
    exists_unrestricted_ordered_ramsey_witness hr2 φ ψ orderA orderB κ
  let D := θ.coboundary hr
  have hD : IsPotential D θ := θ.coboundary_isPotential hr
  refine ⟨X, hX, D, θ, order, hD, hD.isEven, ?_⟩
  intro χ
  let χ' : Embedding (toOrderedNative φ orderA) (toOrderedNative θ order) → κ :=
    fun e => χ (liftPotentialEmbedding hA hD orderA order e)
  obtain ⟨f, hf⟩ := arrow χ'
  refine ⟨liftPotentialEmbedding hB hD orderB order f, ?_⟩
  intro e₁ e₂
  have hh := hf (forgetPotentialEmbedding orderA orderB e₁)
    (forgetPotentialEmbedding orderA orderB e₂)
  have he (e : Embedding (toOrderedPotential A φ orderA) (toOrderedPotential B ψ orderB)) :
      liftPotentialEmbedding hA hD orderA order
          (f.comp (forgetPotentialEmbedding orderA orderB e)) =
        (liftPotentialEmbedding hB hD orderB order f).comp e := by
    apply Embedding.ext
    intro x
    rfl
  change χ (liftPotentialEmbedding hA hD orderA order
      (f.comp (forgetPotentialEmbedding orderA orderB e₁))) =
    χ (liftPotentialEmbedding hA hD orderA order
      (f.comp (forgetPotentialEmbedding orderA orderB e₂))) at hh
  simpa only [he] using hh

/-- The freely ordered class of finite even hypertournaments equipped with
an alternating potential is Ramsey, including the ternary/binary base case. -/
theorem potential_expansions_ramsey {r : ℕ} (hr : Even r) (hr2 : 2 ≤ r) :
    CCO.UnaryHN.Native.Ramsey.{0,v,w} (potentialExpansionClass (r := r)) := by
  intro V W _ _ A B hA hB κ _ _
  rcases hA with ⟨hV, AA, φ, orderA, hφ, rfl⟩
  rcases hB with ⟨hW, BB, ψ, orderB, hψ, rfl⟩
  let : Finite V := hV
  let : Finite W := hW
  obtain ⟨X, hX, D, θ, order, hD, _, arrow⟩ :=
    exists_potential_ramsey_witness hr hr2 AA BB φ ψ hφ hψ orderA orderB κ
  exact ⟨X, hX, toOrderedPotential D θ order, ⟨hX, D, θ, order, hD, rfl⟩, arrow⟩

end Hypertournaments.Ramsey
