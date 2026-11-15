import Hypertournaments.FiniteClassAmalgamation
import Hypertournaments.Fraisse.Unbounded

/-!
# Bounded local constraints and a single forbidden structure

Source: `tex_hypertournaments`, commit
`64a392aa2b0e497c297f1218be3f1a8761bae18d`,
`obs:strict-constrained-hierarchy`. Constraints use arbitrary induced
embeddings, and their sizes are bounded above rather than required to be equal.
-/

namespace Hypertournaments

/-- A class is `k`-constrained if some forbidden family on at most `k`
vertices defines it. The family need not be presented up to isomorphism:
omission already quantifies over all orientation-preserving injections. -/
def FiniteClass.KConstrained {n : ℕ} (K : FiniteClass n) (k : ℕ) : Prop :=
  ∃ family : ForbiddenFamily n,
    (∀ m F, F ∈ family m → m ≤ k) ∧
      ∀ m (A : Hyper n (Fin m)), K m A ↔ Omits family A

/-- Exactly one displayed structure is forbidden. Its other copies are
excluded through the intrinsic embeddings in `Omits`. -/
def singleForbiddenFamily {n k : ℕ} (F : Hyper n (Fin k)) : ForbiddenFamily n :=
  fun m => {A | ∃ h : m = k, h ▸ A = F}

theorem mem_singleForbiddenFamily {n k : ℕ} (F : Hyper n (Fin k)) :
    F ∈ singleForbiddenFamily F k := ⟨rfl, rfl⟩

theorem singleForbiddenFamily_pairCancelling {n k : ℕ} {F : Hyper n (Fin k)}
    (hF : PairCancelling F) :
    ∀ m A, A ∈ singleForbiddenFamily F m → PairCancelling A := by
  intro m A hA
  obtain ⟨h, hA⟩ := hA
  subst m
  have hEq : A = F := by simpa using hA
  exact hEq ▸ hF

theorem omits_singleForbiddenFamily_iff {n k : ℕ} (F : Hyper n (Fin k))
    {V : Type*} (A : Hyper n V) :
    Omits (singleForbiddenFamily F) A ↔ ∀ e : Fin k ↪ V, ¬ Preserves F A e := by
  constructor
  · intro h e
    exact h k F (mem_singleForbiddenFamily F) e
  · intro h m B hB e
    obtain ⟨hm, hB⟩ := hB
    subst m
    have hEq : B = F := by simpa using hB
    rw [hEq]
    exact h e

abbrev singleForbiddenClass {n k : ℕ} (F : Hyper n (Fin k)) : FiniteClass n :=
  fun _ A => Omits (singleForbiddenFamily F) A

theorem singleForbiddenClass_small {n k m : ℕ} (F : Hyper n (Fin k))
    (hm : m < k) (A : Hyper n (Fin m)) : singleForbiddenClass F m A := by
  change Omits (singleForbiddenFamily F) A
  rw [omits_singleForbiddenFamily_iff]
  intro e _
  have h := Fintype.card_le_of_injective e e.injective
  simp only [Fintype.card_fin] at h
  omega

theorem singleForbiddenClass_excludes {n k : ℕ} (F : Hyper n (Fin k)) :
    ¬ singleForbiddenClass F k F := by
  intro h
  exact h k F (mem_singleForbiddenFamily F) (Function.Embedding.refl _) (fun _ => rfl)

theorem singleForbiddenClass_constrained {n k : ℕ} (F : Hyper n (Fin k)) :
    (singleForbiddenClass F).KConstrained k := by
  refine ⟨singleForbiddenFamily F, ?_, fun _ _ => Iff.rfl⟩
  intro m A hA
  exact hA.choose.le

/-- No alternative description by smaller forbidden structures can define
this class: every such proposed obstruction is itself admitted. -/
theorem singleForbiddenClass_not_constrained {n k b : ℕ} (F : Hyper n (Fin k))
    (hb : b < k) : ¬ (singleForbiddenClass F).KConstrained b := by
  intro ⟨family, hbound, hclass⟩
  have hnone : ∀ m A, A ∈ family m → False := by
    intro m A hA
    have hsmall := singleForbiddenClass_small F ((hbound m A hA).trans_lt hb) A
    have hOmit := (hclass m A).mp hsmall
    exact hOmit m A hA (Function.Embedding.refl _) (fun _ => rfl)
  apply singleForbiddenClass_excludes F
  apply (hclass k F).mpr
  intro m A hA
  exact (hnone m A hA).elim

theorem singleForbiddenClass_hereditary {n k : ℕ} (F : Hyper n (Fin k)) :
    (singleForbiddenClass F).Hereditary :=
  FiniteClass.hereditary_omits _

theorem singleForbiddenClass_unbounded {n k : ℕ} {F : Hyper n (Fin k)}
    (hF : PairCancelling F) : (singleForbiddenClass F).Unbounded :=
  pair_cancelling_omission_unbounded hF.1 _ (singleForbiddenFamily_pairCancelling hF)

theorem singleForbiddenClass_hasSAP {n k : ℕ} {F : Hyper n (Fin k)}
    (hF : PairCancelling F) : (singleForbiddenClass F).HasSAP :=
  pair_cancelling_hasStrongAmalgamation hF.1 _ (singleForbiddenFamily_pairCancelling hF)

end Hypertournaments
