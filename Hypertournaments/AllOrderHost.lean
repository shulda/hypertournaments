import Hypertournaments.OrderedJointEmbedding
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Sort

/-!
# One finite host for every order of a fixed hypertournament

Permutations of one fixed finite carrier enumerate the order expansions up to
ordered isomorphism. The host is chosen before either source or target orders
in the eventual ordering-property argument. A supplied finite anchor can be
the ordered two-point structure used for the pair-coloring Ramsey argument.
-/

universe v

namespace Hypertournaments.Ramsey

open StructuralRamsey
open StructuralRamsey.Structure

/-- Two finite orders of the same carrier are related by an explicit order
isomorphism, through their increasing enumerations. -/
noncomputable def orderChange {V : Type v} [Fintype V]
    (source target : LinearOrder V) : @OrderIso V V source.toLE target.toLE :=
  @OrderIso.trans V (Fin (Fintype.card V)) V source.toLE inferInstance target.toLE
    (@OrderIso.symm (Fin (Fintype.card V)) V inferInstance source.toLE
      (@Fintype.orderIsoFinOfCardEq V source inferInstance (Fintype.card V) rfl))
    (@Fintype.orderIsoFinOfCardEq V target inferInstance (Fintype.card V) rfl)

/-- An arbitrary source order embeds in its permutation-reindexed copy with
one fixed canonical order; the intrinsic orientation is unchanged. -/
noncomputable def orderExpansionReindex {n : ℕ} {V : Type v} [Fintype V]
    (A : Hyper n V) (canonical orderA : LinearOrder V) :
    Embedding (toOrderedNative A orderA)
      (toOrderedNative (A.pullback (orderChange canonical orderA).toEquiv.toEmbedding) canonical) := by
  let σ := orderChange canonical orderA
  let e : @OrderEmbedding V V orderA.toLE canonical.toLE :=
    @OrderIso.toOrderEmbedding V V orderA.toLE canonical.toLE
      (@OrderIso.symm V V canonical.toLE orderA.toLE σ)
  apply @orderedEmbedding n V V orderA canonical A (A.pullback σ.toEquiv.toEmbedding) e
  intro t
  change A.orient ((t.trans e.toEmbedding).trans σ.toEquiv.toEmbedding) = A.orient t
  congr 1
  ext k
  exact σ.toEquiv.apply_symm_apply (t k)

/-- There is one finite ordered omission-class host containing every order
expansion of A and also the fixed anchor P. The host does not depend on a
subsequently chosen source order. -/
theorem exists_all_order_host_with {n : ℕ} (hn : 3 ≤ n)
    (family : ForbiddenFamily n) (hpc : ∀ m F, F ∈ family m → PairCancelling F)
    {V U : Type v} [Finite V] [Finite U]
    (A : Hyper n V) (hA : Omits family A)
    (P : Hyper n U) (orderP : LinearOrder U) (hP : Omits family P) :
    ∃ (W : Type v) (_ : Finite W) (D : Hyper n W) (orderD : LinearOrder W),
      Omits family D ∧
      (∀ orderA : LinearOrder V,
        Nonempty (Embedding (toOrderedNative A orderA) (toOrderedNative D orderD))) ∧
      Nonempty (Embedding (toOrderedNative P orderP) (toOrderedNative D orderD)) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let e := Fintype.equivFin V
  let canonical : LinearOrder V := LinearOrder.lift' e e.injective
  let models : Equiv.Perm V → Structure (orderedLanguage n) V :=
    fun σ => toOrderedNative (A.pullback σ.toEmbedding) canonical
  have hmodels : ∀ σ, orderedOmissionClass family (models σ) := by
    intro σ
    exact ⟨inferInstance, A.pullback σ.toEmbedding, canonical,
      omits_pullback hA σ.toEmbedding, rfl⟩
  have hanchor : orderedOmissionClass family (toOrderedNative P orderP) :=
    ⟨inferInstance, P, orderP, hP, rfl⟩
  obtain ⟨W, hW, C, hC, hAnchor, hEach⟩ :=
    all_finite_ordered_jointEmbedding hn family hpc (fun _ : Equiv.Perm V => V)
      models hmodels (toOrderedNative P orderP) hanchor
  rcases hC with ⟨_, D, orderD, hD, rfl⟩
  refine ⟨W, hW, D, orderD, hD, ?_, hAnchor⟩
  intro orderA
  let σ : Equiv.Perm V := (orderChange canonical orderA).toEquiv
  obtain ⟨j⟩ := hEach σ
  exact ⟨j.comp (orderExpansionReindex A canonical orderA)⟩

end Hypertournaments.Ramsey
