import Hypertournaments.LocalForbiddenFamily
import Hypertournaments.PairRamsey
import Hypertournaments.PairOrdering

/-!
# Ramsey and ordering witnesses for the positive local-index classes

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`thm:Ramsey`, `thm:ordering`, and the local-type classification.
When both central types are allowed, the actual forbidden packets satisfy
pair-cancellation. The returned structures are admissible for the original S.
-/

universe v w

namespace Hypertournaments.Ramsey

open StructuralRamsey
open StructuralRamsey.Structure

/-- Actual finite admissible Ramsey witnesses for the central/next-central
branch, for every finite nonempty colour palette. -/
theorem exists_local_class_ramsey_witness {n : ℕ} (hn : 3 ≤ n)
    (S : Set ℕ) (hcentral : centralIndex n ∈ S) (hnext : nextCentralIndex n ∈ S)
    {V W : Type v} [Finite V] [Finite W]
    (A : Hyper n V) (B : Hyper n W) (orderA : LinearOrder V) (orderB : LinearOrder W)
    (hA : Admissible S A) (hB : Admissible S B)
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    ∃ (X : Type v) (_ : Finite X) (D : Hyper n X) (order : LinearOrder X),
      Admissible S D ∧ Structure.Arrow (toOrderedNative A orderA)
        (toOrderedNative B orderB) (toOrderedNative D order) κ := by
  obtain ⟨X, hX, D, order, hD, arrow⟩ := exists_ordered_ramsey_witness hn
    (localForbiddenFamily n S) (localForbiddenFamily_pairCancelling hn S hcentral hnext)
    A B orderA orderB ((omits_localForbiddenFamily_iff_admissible S A).mpr hA)
    ((omits_localForbiddenFamily_iff_admissible S B).mpr hB) κ
  exact ⟨X, hX, D, order, (omits_localForbiddenFamily_iff_admissible S D).mp hD, arrow⟩

/-- One admissible target is chosen before both free vertex orders. -/
theorem local_class_ordering_property {n : ℕ} (hn : 3 ≤ n)
    (S : Set ℕ) (hcentral : centralIndex n ∈ S) (hnext : nextCentralIndex n ∈ S)
    {V : Type} [Finite V] (A : Hyper n V) (hA : Admissible S A) :
    ∃ (W : Type) (_ : Finite W) (B : Hyper n W), Admissible S B ∧
      ∀ (orderA : LinearOrder V) (orderB : LinearOrder W),
        Nonempty (Embedding (toOrderedNative A orderA) (toOrderedNative B orderB)) := by
  obtain ⟨W, hW, B, hB, hAll⟩ := pair_cancelling_ordering_property hn
    (localForbiddenFamily n S) (localForbiddenFamily_pairCancelling hn S hcentral hnext)
    A ((omits_localForbiddenFamily_iff_admissible S A).mpr hA)
  exact ⟨W, hW, B, (omits_localForbiddenFamily_iff_admissible S B).mp hB, hAll⟩

end Hypertournaments.Ramsey
