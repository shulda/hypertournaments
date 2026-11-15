import Hypertournaments.ContinuumFamily
import Hypertournaments.Fraisse.OmissionLimit
import Hypertournaments.PairOrdering

/-!
# Continuum many homogeneous hypertournaments with freely ordered Ramsey ages

The finite antichain is the only input to this final assembly. Every limit is
constructed internally, and its actual age is identified with the corresponding
omission class. In particular, nonisomorphism follows from finite structures
which occur in one age and are forbidden in the other.
-/

namespace Hypertournaments

namespace Hyper

/-- Membership in the actual age, on any finite presentation. -/
def AgeContains {n : ℕ} {V W : Type*} (M : Hyper n V) (B : Hyper n W) : Prop :=
  ∃ e : W ↪ V, Preserves B M e

/-- The finite-cardinality presentation of the actual age. -/
def finiteAge {n : ℕ} {V : Type*} (M : Hyper n V) : FiniteHyperClass n :=
  fun _ B => M.AgeContains B

/-- Freely ordered expansions of finite members of the actual age. -/
def orderedAge {n : ℕ} {V : Type*} (M : Hyper n V) {W : Type}
    (C : StructuralRamsey.Structure (Ramsey.orderedLanguage n) W) : Prop :=
  Finite W ∧ ∃ (B : Hyper n W) (order : LinearOrder W),
    M.AgeContains B ∧ C = Ramsey.toOrderedNative B order

/-- Intrinsic isomorphisms preserve the actual finite age. -/
theorem finiteAge_eq_of_isomorphic {n : ℕ} {V W : Type*}
    {M : Hyper n V} {N : Hyper n W} (h : M.Isomorphic N) :
    M.finiteAge = N.finiteAge := by
  obtain ⟨e, he⟩ := h
  funext m B
  apply propext
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f.trans e.toEmbedding, ?_⟩
    intro t
    exact (he (t.trans f)).trans (hf t)
  · rintro ⟨f, hf⟩
    refine ⟨f.trans e.symm.toEmbedding, ?_⟩
    intro t
    exact (preserves_symm he (t.trans f)).trans (hf t)

/-- Equality on the `Fin m` skeleton identifies age membership on every finite
carrier, including the carriers produced by the Ramsey and ordering witnesses. -/
theorem ageContains_iff_omits {n : ℕ} {V : Type*} (M : Hyper n V)
    (family : ForbiddenFamily n) (hAge : M.finiteAge = omissionClass family)
    {W : Type} [Finite W] (B : Hyper n W) :
    M.AgeContains B ↔ Omits family B := by
  classical
  let : Fintype W := Fintype.ofFinite W
  let e : Fin (Fintype.card W) ≃ W := (Fintype.equivFin W).symm
  let C := B.pullback e.toEmbedding
  have he : Preserves C B e.toEmbedding := fun _ => rfl
  have hC : M.AgeContains C ↔ Omits family C := by
    change C ∈ M.finiteAge (Fintype.card W) ↔ C ∈ omissionClass family (Fintype.card W)
    rw [hAge]
  constructor
  · rintro ⟨f, hf⟩
    have hEmb : M.AgeContains C := by
      refine ⟨e.toEmbedding.trans f, ?_⟩
      intro t
      exact (hf (t.trans e.toEmbedding)).trans (he t)
    exact omits_of_preserves (preserves_symm he) (hC.mp hEmb)
  · intro hB
    obtain ⟨f, hf⟩ := hC.mpr (omits_pullback hB e.toEmbedding)
    refine ⟨e.symm.toEmbedding.trans f, ?_⟩
    intro t
    exact (hf (t.trans e.symm.toEmbedding)).trans (preserves_symm he t)

theorem orderedAge_iff_omissionClass {n : ℕ} {V : Type*} (M : Hyper n V)
    (family : ForbiddenFamily n) (hAge : M.finiteAge = omissionClass family)
    {W : Type} (C : StructuralRamsey.Structure (Ramsey.orderedLanguage n) W) :
    M.orderedAge C ↔ Ramsey.orderedOmissionClass family C := by
  constructor
  · rintro ⟨hW, B, order, hB, rfl⟩
    let := hW
    exact ⟨hW, B, order, (ageContains_iff_omits M family hAge B).mp hB, rfl⟩
  · rintro ⟨hW, B, order, hB, rfl⟩
    let := hW
    exact ⟨hW, B, order, (ageContains_iff_omits M family hAge B).mpr hB, rfl⟩

/-- The ordering witness is fixed before either of its two free orders. -/
def AgeHasOrderingProperty {n : ℕ} {V : Type*} (M : Hyper n V) : Prop :=
  ∀ {W : Type} [Finite W] (B : Hyper n W), M.AgeContains B →
    ∃ (X : Type) (_ : Finite X) (D : Hyper n X), M.AgeContains D ∧
      ∀ (orderB : LinearOrder W) (orderD : LinearOrder X),
        Nonempty (StructuralRamsey.Structure.Embedding
          (Ramsey.toOrderedNative B orderB) (Ramsey.toOrderedNative D orderD))

end Hyper

/-- A genuinely countably infinite homogeneous intrinsic hypertournament. -/
structure CountableHomogeneousHyper (n : ℕ) where
  Carrier : Type
  [countable : Countable Carrier]
  [infinite : Infinite Carrier]
  hyper : Hyper n Carrier
  homogeneous : hyper.Homogeneous

attribute [instance] CountableHomogeneousHyper.countable CountableHomogeneousHyper.infinite

/-- An explicit continuum family. All assertions concern the actual constructed
structures and their actual ages; the forbidden families record the exact ages. -/
structure ContinuumHomogeneousFamily (n : ℕ) where
  forbidden : Set ℕ → ForbiddenFamily n
  model : Set ℕ → CountableHomogeneousHyper n
  finite_age : ∀ S, (model S).hyper.finiteAge = omissionClass (forbidden S)
  nonisomorphic : ∀ S T, S ≠ T → ¬ (model S).hyper.Isomorphic (model T).hyper
  ramsey : ∀ S, CCO.UnaryHN.Native.Ramsey.{0,0,0} (model S).hyper.orderedAge
  ordering : ∀ S, (model S).hyper.AgeHasOrderingProperty
  continuum_many_ages : Cardinal.mk (Set.range (fun S => (model S).hyper.finiteAge)) =
    Cardinal.continuum
  not_finitelyBounded : ∀ S, ¬ ClassFinitelyBounded (model S).hyper.finiteAge

namespace ContinuumHomogeneousFamily

private noncomputable def omissionModel {n : ℕ} (hn : 3 ≤ n)
    (family : ForbiddenFamily n) (hpc : ∀ m F, F ∈ family m → PairCancelling F) :
    CountableHomogeneousHyper n where
  Carrier := Fraisse.OmissionLimit.Carrier hn family hpc
  countable := inferInstance
  infinite := inferInstance
  hyper := Fraisse.OmissionLimit.hyper hn family hpc
  homogeneous := Fraisse.OmissionLimit.homogeneous hn family hpc

private theorem omissionModel_age {n : ℕ} (hn : 3 ≤ n)
    (family : ForbiddenFamily n) (hpc : ∀ m F, F ∈ family m → PairCancelling F) :
    (omissionModel hn family hpc).hyper.finiteAge = omissionClass family := by
  funext m B
  apply propext
  exact Fraisse.OmissionLimit.finite_age hn family hpc m B

/-- Assemble the continuum family from an actual pair-cancelling antichain.
The odd forbidden indices are always selected, so every age additionally has
no finite forbidden basis. -/
noncomputable def ofAntichain {n : ℕ} (hn : 3 ≤ n) (A : IndexedPCAntichain n) :
    ContinuumHomogeneousFamily n := by
  let family := fun S => selectedForbiddenFamily A (infiniteSelection S)
  have hpc S : ∀ m F, F ∈ family S m → PairCancelling F :=
    selectedForbiddenFamily_pairCancelling A (infiniteSelection S)
  let model := fun S => omissionModel hn (family S) (hpc S)
  have hAge S : (model S).hyper.finiteAge = omissionClass (family S) :=
    omissionModel_age hn (family S) (hpc S)
  refine {
    forbidden := family
    model := model
    finite_age := hAge
    nonisomorphic := ?_
    ramsey := ?_
    ordering := ?_
    continuum_many_ages := ?_
    not_finitelyBounded := ?_ }
  · intro S T hST hIso
    have hEq := Hyper.finiteAge_eq_of_isomorphic hIso
    rw [hAge S, hAge T] at hEq
    exact hST (infiniteSelection_injective
      (omissionClass_selectedForbiddenFamily_injective A hEq))
  · intro S
    have hEq : @Hyper.orderedAge n _ (model S).hyper =
        @Ramsey.orderedOmissionClass n (family S) := by
      funext W C
      exact propext (Hyper.orderedAge_iff_omissionClass (model S).hyper (family S) (hAge S) C)
    rw [hEq]
    exact @Ramsey.pair_cancelling_ordered_ramsey.{0,0} n hn (family S) (hpc S)
  · intro S W hW B hB
    have hOmit := (Hyper.ageContains_iff_omits (model S).hyper (family S) (hAge S) B).mp hB
    obtain ⟨X, hX, D, hD, hOrder⟩ :=
      Ramsey.pair_cancelling_ordering_property hn (family S) (hpc S) B hOmit
    let := hX
    exact ⟨X, hX, D,
      (Hyper.ageContains_iff_omits (model S).hyper (family S) (hAge S) D).mpr hD, hOrder⟩
  · have hEq : (fun S => (model S).hyper.finiteAge) =
        (fun S => omissionClass (family S)) := funext hAge
    rw [hEq]
    exact selected_infinite_classes_cardinality A
  · intro S
    rw [hAge S]
    exact selected_omissionClass_not_finitelyBounded A (infiniteSelection_infinite S)

end ContinuumHomogeneousFamily

end Hypertournaments
