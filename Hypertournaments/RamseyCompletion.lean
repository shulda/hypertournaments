import Hypertournaments.RamseyPartial
import Hypertournaments.RamseyRelationalIrreducible
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FinCases

/-!
# Same-carrier relational completions and native homomorphism-embeddings

The input is an arbitrary R,< structure whose old irreducible pieces are
ordered forbidden-free hypertournaments. Completion adds relations globally
and reflects them on every old irreducible source, as required by native HN.
-/

universe v

namespace Hypertournaments.Ramsey

open StructuralRamsey
open StructuralRamsey.Structure

variable {n : ℕ} {V : Type v}

/-- With no function symbols the native weak-global and full-global
homomorphism-embedding interfaces agree, for arbitrary vertex maps. -/
theorem fullHE_iff_nativeHE {W : Type v}
    (C : Structure (orderedLanguage n) V) (D : Structure (orderedLanguage n) W)
    (f : V → W) : C.IsHomomorphismEmbedding D f ↔ C.IsEHNHomomorphismEmbedding D f := by
  constructor
  · intro h
    exact ⟨⟨h.1.1, by intro F; exact nomatch F⟩, h.2⟩
  · intro h
    exact ⟨⟨h.1.1, by intro F; exact nomatch F⟩, h.2⟩

/-- Extending the extracted orientation and the old comparisons gives the
actual native HN homomorphism-embedding on the unchanged carrier. -/
theorem nativeHE_of_completion
    (family : ForbiddenFamily n) (C : Structure (orderedLanguage n) V)
    (hIrr : CCO.UnaryHN.Native.IrreduciblesIn (orderedOmissionClass family) C)
    (order : LinearOrder V)
    (hExt : ∀ x y, C.rel (.inr ()) ![x, y] → @LT.lt V order.toLT x y)
    (D : Hyper n V) (hD : (partialOrientation family C hIrr).Extends D) :
    C.IsEHNHomomorphismEmbedding (toOrderedNative D order) id := by
  classical
  constructor
  · constructor
    · intro R t ht
      cases R with
      | inl R =>
        cases R
        have hinj := positive_relation_injective family C hIrr t ht
        let f : Fin n ↪ V := ⟨t, hinj⟩
        have hcl : ComparisonClique C (Set.range f) :=
          positive_relation_clique family C hIrr t ht
        have hp : (partialOrientation family C hIrr).orient f = some false := by
          simp only [partialOrientation, ite_eq_left hcl]
          simp only [rawSign, show C.rel (.inl ()) f from ht, ite_eq_left]
        change D.Relation t
        exact ⟨hinj, hD f false hp⟩
      | inr R =>
        cases R
        change Fin 2 → V at t
        change @LT.lt V order.toLT (t 0) (t 1)
        apply hExt
        have heq : ![t 0, t 1] = t := by
          funext i
          fin_cases i <;> rfl
        exact heq.symm ▸ ht
    · intro F
      exact nomatch F
  · intro X E hE e
    obtain ⟨_, A, oE, _, hmodel⟩ := hIrr E hE e
    subst E
    let ee : X ↪ V := e.toFunctionEmbedding
    have hPres : Preserves A D ee := by
      intro f
      have hcl : ComparisonClique C (Set.range (f.trans ee)) := by
        intro x hx y hy hxy
        obtain ⟨i, rfl⟩ := hx
        obtain ⟨j, rfl⟩ := hy
        exact comparisonClique_image A oE C e _ ⟨f i, rfl⟩ _ ⟨f j, rfl⟩ hxy
      have hp : (partialOrientation family C hIrr).orient (f.trans ee) = some (A.orient f) := by
        simp only [partialOrientation, ite_eq_left hcl]
        exact congrArg some (rawSign_of_embedding A oE C e f)
      exact hD _ _ hp
    let : LinearOrder X := oE
    let : LinearOrder V := order
    have hm : StrictMono (e : X → V) := by
      intro x y hxy
      apply hExt
      have h := (e.map_rel_iff (.inr ()) ![x, y]).mpr hxy
      have heq : e ∘ ![x, y] = ![e x, e y] := by
        funext i
        fin_cases i <;> rfl
      exact heq ▸ h
    let eo : X ↪o V := OrderEmbedding.ofStrictMono e hm
    exact ⟨orderedEmbedding A D eo hPres, fun _ => rfl⟩

/-- A finite arbitrary relational input satisfying the completion hypotheses
has an actual forbidden-free completion on the identical carrier. -/
theorem exists_native_strong_completion (hn : 3 ≤ n)
    (family : ForbiddenFamily n) (hpc : ∀ m F, F ∈ family m → PairCancelling F)
    [Finite V] (C : Structure (orderedLanguage n) V)
    (hIrr : CCO.UnaryHN.Native.IrreduciblesIn (orderedOmissionClass family) C)
    (order : LinearOrder V)
    (hExt : ∀ x y, C.rel (.inr ()) ![x, y] → @LT.lt V order.toLT x y) :
    ∃ D : Hyper n V, Omits family D ∧
      C.IsEHNHomomorphismEmbedding (toOrderedNative D order) id := by
  classical
  let : LinearOrder V := order
  let : Fintype V := Fintype.ofFinite V
  obtain ⟨D, hPD, hD⟩ := exists_pair_cancelling_completion (by omega)
    (partialOrientation family C hIrr) (missingPairs C) (missingPairs_distinct C)
    (partial_cliqueDomain family C hIrr) family hpc (partial_omits family hpc C hIrr)
  exact ⟨D, hD, nativeHE_of_completion family C hIrr order hExt D hPD⟩

/-- Native-interface same-carrier completion: arbitrary
R,< input, a linear extension of its comparisons, and genuine membership of
all old irreducible pieces suffice. -/
theorem exists_native_relational_completion (hn : 3 ≤ n)
    (family : ForbiddenFamily n) (hpc : ∀ m F, F ∈ family m → PairCancelling F)
    [Finite V] (C : Structure (orderedLanguage n) V)
    (hIrr : CCO.UnaryHN.Native.IrreduciblesIn (orderedOmissionClass family) C)
    (hOrder : ∃ order : LinearOrder V,
      ∀ x y, C.rel (.inr ()) ![x, y] → @LT.lt V order.toLT x y) :
    ∃ (order : LinearOrder V) (D : Hyper n V), Omits family D ∧
      C.IsHomomorphismEmbedding (toOrderedNative D order) id := by
  obtain ⟨order, hExt⟩ := hOrder
  obtain ⟨D, hD, hHE⟩ := exists_native_strong_completion hn family hpc C hIrr order hExt
  exact ⟨order, D, hD, (fullHE_iff_nativeHE C (toOrderedNative D order) id).mpr hHE⟩

/-- The paper's pair-coverage formulation of irreducible-piece membership. -/
def RelationalIrreduciblesIn (family : ForbiddenFamily n)
    (C : Structure (orderedLanguage n) V) : Prop :=
  ∀ {X : Type v} (E : Structure (orderedLanguage n) X), PairCovered E →
    Embedding E C → orderedOmissionClass family E

theorem relationalIrreduciblesIn_iff_native
    (family : ForbiddenFamily n) (C : Structure (orderedLanguage n) V) :
    RelationalIrreduciblesIn family C ↔
      CCO.UnaryHN.Native.IrreduciblesIn (orderedOmissionClass family) C := by
  constructor
  · intro h X E hE e
    exact h E ((irreducible_iff_pair_coverage E).mp hE) e
  · intro h X E hE e
    exact h E ((irreducible_iff_pair_coverage E).mpr hE) e

/-- The article's original arbitrary-relational completion theorem, with
pair-covered irreducibles and an extendible partial comparison relation. -/
theorem exists_relational_completion (hn : 3 ≤ n)
    (family : ForbiddenFamily n) (hpc : ∀ m F, F ∈ family m → PairCancelling F)
    [Finite V] (C : Structure (orderedLanguage n) V)
    (hIrr : RelationalIrreduciblesIn family C)
    (hOrder : ∃ order : LinearOrder V,
      ∀ x y, C.rel (.inr ()) ![x, y] → @LT.lt V order.toLT x y) :
    ∃ (order : LinearOrder V) (D : Hyper n V), Omits family D ∧
      C.IsHomomorphismEmbedding (toOrderedNative D order) id :=
  exists_native_relational_completion hn family hpc C
    ((relationalIrreduciblesIn_iff_native family C).mp hIrr) hOrder

end Hypertournaments.Ramsey
