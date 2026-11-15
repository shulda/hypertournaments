import Hypertournaments.PotentialLanguage
import Hypertournaments.EvenPotentialGauge
import Hypertournaments.PotentialGaugeHomogeneity
import Hypertournaments.BinaryOrdering

/-!
# The full expansion property for even hypertournaments

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`thm:potential`, and the expanded proof preparation section 4.

The finite witness is chosen before either potential or either free order.
A Ramsey-homogeneous symmetric gauge has zero coboundary in the even
potential arity; its common colour itself need not be zero.
-/

namespace Hypertournaments.Ramsey

open StructuralRamsey
open StructuralRamsey.Structure

private theorem finite_hyper {r : ℕ} {V : Type} [Finite V] : Finite (Hyper r V) :=
  Finite.of_injective (fun A : Hyper r V => A.orient)
    (fun _ _ h => Hyper.ext (congrFun h))

/-- One finite ordered host contains every potential on a fixed finite
carrier, with every choice of free order. It also retains a chosen anchor.
Enumerating all lower orientations is stronger than enumerating only the
potentials of one fixed upper structure. -/
theorem exists_all_potential_order_host {r : ℕ} (hr2 : 2 ≤ r)
    {V U : Type} [Finite V] [Finite U]
    (anchor : Hyper r U) (orderAnchor : LinearOrder U) :
    ∃ (W : Type) (_ : Finite W) (D : Hyper r W) (orderD : LinearOrder W),
      (∀ (φ : Hyper r V) (orderφ : LinearOrder V),
        Nonempty (Embedding (toOrderedNative φ orderφ) (toOrderedNative D orderD))) ∧
      Nonempty (Embedding (toOrderedNative anchor orderAnchor) (toOrderedNative D orderD)) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let : Finite (Hyper r V) := finite_hyper
  let : Fintype (Hyper r V) := Fintype.ofFinite _
  let e := Fintype.equivFin V
  let canonical : LinearOrder V := LinearOrder.lift' e e.injective
  let models : Hyper r V → Structure (orderedLanguage r) V :=
    fun φ => toOrderedNative φ canonical
  have hmodels : ∀ φ, orderedOmissionClass (emptyForbiddenFamily r) (models φ) := by
    intro φ
    exact ⟨inferInstance, φ, canonical, omits_emptyForbiddenFamily φ, rfl⟩
  have hanchor : orderedOmissionClass (emptyForbiddenFamily r)
      (toOrderedNative anchor orderAnchor) :=
    ⟨inferInstance, anchor, orderAnchor, omits_emptyForbiddenFamily anchor, rfl⟩
  obtain ⟨W, hW, E, hE, hAnchor, hEach⟩ :=
    unrestricted_finite_ordered_jointEmbedding hr2 Finset.univ (fun _ : Hyper r V => V)
      models hmodels (toOrderedNative anchor orderAnchor) hanchor
  have hEachAll : ∀ φ, Nonempty (Embedding (models φ) E) :=
    fun φ => hEach φ (Finset.mem_univ _)
  rcases hE with ⟨_, D, orderD, _, rfl⟩
  refine ⟨W, hW, D, orderD, ?_, hAnchor⟩
  intro φ orderφ
  let σ := (orderChange canonical orderφ).toEquiv
  obtain ⟨j⟩ := hEachAll (φ.pullback σ.toEmbedding)
  exact ⟨j.comp (orderExpansionReindex φ canonical orderφ)⟩

/-- The full expansion property relative to the finite even reduct class.
The upper witness B is fixed before all source and target potentials and
orders are chosen. Both named orientations are preserved by the final map. -/
theorem potential_expansion_property {r : ℕ} (hr : Even r) (hr2 : 2 ≤ r)
    {V : Type} [Finite V] (A : Hyper (r + 1) V) (_hA : A.IsEven) :
    ∃ (W : Type) (_ : Finite W) (B : Hyper (r + 1) W), B.IsEven ∧
      ∀ (φ : Hyper r V) (orderA : LinearOrder V)
        (ψ : Hyper r W) (orderB : LinearOrder W),
        IsPotential A φ → IsPotential B ψ →
          Nonempty (Embedding (toOrderedPotential A φ orderA) (toOrderedPotential B ψ orderB)) := by
  classical
  have hrpos : 0 < r := by omega
  let P := smallGaugeModel r
  let orderP : LinearOrder (Fin (r - 1)) := inferInstance
  obtain ⟨U, hU, D, orderD, hAll, _hAnchor⟩ :=
    exists_all_potential_order_host (V := V) hr2 P orderP
  let : Finite U := hU
  obtain ⟨X, hX, C, orderC, _, arrow⟩ :=
    exists_unrestricted_ordered_ramsey_witness hr2 P D orderP orderD (ZMod 2)
  let : Finite X := hX
  obtain ⟨W, hW, φ₀, hOP⟩ := unrestricted_ordering_property hr2 C
  let : Finite W := hW
  let B := φ₀.coboundary hr
  refine ⟨W, hW, B, φ₀.isEven_coboundary hr, ?_⟩
  intro φ orderA ψ orderB hφ hψ
  obtain ⟨z, hz⟩ := hψ.intrinsic_gauge (φ₀.coboundary_isPotential hr) hrpos
  obtain ⟨f⟩ := hOP orderC orderB
  let colour : Embedding (toOrderedNative P orderP) (toOrderedNative C orderC) → ZMod 2 :=
    fun e => z (tupleVertices (e.toFunctionEmbedding.trans f.toFunctionEmbedding))
  obtain ⟨g, hg⟩ := arrow colour
  let h := f.comp g
  have hhom : ∀ e₁ e₂ : Embedding (orderedSmallGaugeModel r) (toOrderedNative D orderD),
      z (tupleVertices (e₁.toFunctionEmbedding.trans h.toFunctionEmbedding)) =
        z (tupleVertices (e₂.toFunctionEmbedding.trans h.toFunctionEmbedding)) := by
    intro e₁ e₂
    exact hg e₁ e₂
  have hPres : Preserves D ψ h.toFunctionEmbedding :=
    gauge_homogeneity_preserves hr hrpos D orderD φ₀ ψ orderB h z hz hhom
  let eo : @OrderEmbedding U W orderD.toLE orderB.toLE :=
    @OrderEmbedding.ofStrictMono U W orderD orderB.toPreorder h
      (@strictMono_of_orderedEmbedding r U W orderD orderB D φ₀ h)
  let switched : Embedding (toOrderedNative D orderD) (toOrderedNative ψ orderB) :=
    @orderedEmbedding r U W orderD orderB D ψ eo hPres
  obtain ⟨source⟩ := hAll φ orderA
  exact ⟨liftPotentialEmbedding hφ hψ orderA orderB (switched.comp source)⟩

end Hypertournaments.Ramsey
