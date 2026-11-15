import Hypertournaments.UnrestrictedRamsey
import Hypertournaments.AllOrderHost

/-!
# All-order hosts in the unrestricted class, including arity two

The genuine unrestricted SAP is used over an empty root. Finite induction
then joins all permutation presentations of a fixed hypertournament.
-/

universe v w

namespace Hypertournaments.Ramsey

open StructuralRamsey
open StructuralRamsey.Structure

theorem unrestricted_ordered_jointEmbedding {n : ℕ} (hn : 2 ≤ n)
    {V W : Type v} (A : Structure (orderedLanguage n) V) (B : Structure (orderedLanguage n) W)
    (hA : orderedOmissionClass (emptyForbiddenFamily n) A)
    (hB : orderedOmissionClass (emptyForbiddenFamily n) B) :
    ∃ (X : Type v) (_ : Finite X) (D : Structure (orderedLanguage n) X),
      orderedOmissionClass (emptyForbiddenFamily n) D ∧
      Nonempty (Embedding A D) ∧ Nonempty (Embedding B D) := by
  obtain ⟨X, hX, D, hD, i, j, _, _⟩ :=
    (unrestricted_orderedOmissionClass_finiteHereditarySAP hn).strong hA hB
      (emptyOrderedEmbedding (by omega) A) (emptyOrderedEmbedding (by omega) B)
  exact ⟨X, hX, D, hD, ⟨i⟩, ⟨j⟩⟩

theorem unrestricted_finite_ordered_jointEmbedding {n : ℕ} (hn : 2 ≤ n)
    {I : Type w} (indices : Finset I) (Carrier : I → Type v)
    (models : ∀ i, Structure (orderedLanguage n) (Carrier i))
    (hmodels : ∀ i, orderedOmissionClass (emptyForbiddenFamily n) (models i))
    {U : Type v} (anchor : Structure (orderedLanguage n) U)
    (hanchor : orderedOmissionClass (emptyForbiddenFamily n) anchor) :
    ∃ (X : Type v) (_ : Finite X) (D : Structure (orderedLanguage n) X),
      orderedOmissionClass (emptyForbiddenFamily n) D ∧ Nonempty (Embedding anchor D) ∧
      ∀ i ∈ indices, Nonempty (Embedding (models i) D) := by
  classical
  induction indices using Finset.induction_on with
  | empty => exact ⟨U, hanchor.1, anchor, hanchor, ⟨Embedding.id _⟩, by simp⟩
  | @insert i indices hi ih =>
    obtain ⟨X, hX, D, hD, ⟨eAnchor⟩, hEach⟩ := ih
    obtain ⟨Y, hY, E, hE, ⟨eD⟩, ⟨eI⟩⟩ :=
      unrestricted_ordered_jointEmbedding hn D (models i) hD (hmodels i)
    refine ⟨Y, hY, E, hE, ⟨eD.comp eAnchor⟩, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact ⟨eI⟩
    · obtain ⟨ej⟩ := hEach j hj
      exact ⟨eD.comp ej⟩

theorem unrestricted_exists_all_order_host_with {n : ℕ} (hn : 2 ≤ n)
    {V U : Type v} [Finite V] [Finite U]
    (A : Hyper n V) (P : Hyper n U) (orderP : LinearOrder U) :
    ∃ (W : Type v) (_ : Finite W) (D : Hyper n W) (orderD : LinearOrder W),
      (∀ orderA : LinearOrder V,
        Nonempty (Embedding (toOrderedNative A orderA) (toOrderedNative D orderD))) ∧
      Nonempty (Embedding (toOrderedNative P orderP) (toOrderedNative D orderD)) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let e := Fintype.equivFin V
  let canonical : LinearOrder V := LinearOrder.lift' e e.injective
  let models : Equiv.Perm V → Structure (orderedLanguage n) V :=
    fun σ => toOrderedNative (A.pullback σ.toEmbedding) canonical
  have hmodels : ∀ σ, orderedOmissionClass (emptyForbiddenFamily n) (models σ) := by
    intro σ
    exact ⟨inferInstance, A.pullback σ.toEmbedding, canonical,
      omits_emptyForbiddenFamily _, rfl⟩
  have hanchor : orderedOmissionClass (emptyForbiddenFamily n) (toOrderedNative P orderP) :=
    ⟨inferInstance, P, orderP, omits_emptyForbiddenFamily _, rfl⟩
  obtain ⟨W, hW, C, hC, hAnchor, hEach⟩ :=
    unrestricted_finite_ordered_jointEmbedding hn Finset.univ (fun _ : Equiv.Perm V => V)
      models hmodels (toOrderedNative P orderP) hanchor
  have hEachAll : ∀ σ, Nonempty (Embedding (models σ) C) :=
    fun σ => hEach σ (Finset.mem_univ _)
  rcases hC with ⟨_, D, orderD, _, rfl⟩
  refine ⟨W, hW, D, orderD, ?_, hAnchor⟩
  intro orderA
  let σ : Equiv.Perm V := (orderChange canonical orderA).toEquiv
  obtain ⟨j⟩ := hEachAll σ
  exact ⟨j.comp (orderExpansionReindex A canonical orderA)⟩

end Hypertournaments.Ramsey
