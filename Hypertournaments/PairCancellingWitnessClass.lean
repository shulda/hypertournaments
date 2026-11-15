import Lean.Elab.Tactic.Omega
import Hypertournaments.LocalPairCancellationConverse
import Hypertournaments.LocalForbiddenFamily
import Hypertournaments.PairAmalgamation
import Hypertournaments.FiniteHyperClass

/-!
# The common omission class for all pair-cancelling families

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`thm:higharity-no-eppa` (common witness assertion).
-/

namespace Hypertournaments

def allPairCancellingFamily (n : ℕ) : ForbiddenFamily n :=
  fun _ => {F | PairCancelling F}

theorem allPairCancellingFamily_hasStrongAmalgamation {n : ℕ} (hn : 3 ≤ n) :
    HasStrongAmalgamation (allPairCancellingFamily n) :=
  pair_cancelling_hasStrongAmalgamation hn (allPairCancellingFamily n) (fun _ _ h => h)

theorem omits_allPairCancelling_implies {n : ℕ} {V : Type*}
    (family : ForbiddenFamily n) (hpc : ∀ m F, F ∈ family m → PairCancelling F)
    (A : Hyper n V) (hA : Omits (allPairCancellingFamily n) A) : Omits family A := by
  intro m F hF e he
  exact hA m F (hpc m F hF) e he

/-- A packet whose index is one of the two central types omits every
finite pair-cancelling structure, regardless of its cardinality. -/
theorem omits_allPairCancelling_of_packet_index {n : ℕ} (hn : 3 ≤ n)
    (P : Hyper n (Fin (n + 1)))
    (hP : centralIndex n - 1 ≤ localIndex P (Function.Embedding.refl _)) :
    Omits (allPairCancellingFamily n) P := by
  intro m F hF e he
  have hlow : n + 1 ≤ m := by simpa only [Nat.card_fin] using hF.2.1
  have hupp : m ≤ n + 1 := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e e.injective
  have hm : m = n + 1 := by omega
  subst m
  have hsmall := localIndex_le_of_pairCancelling hn F hF
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.ofBijective e
    ⟨e.injective, Finite.surjective_of_injective e.injective⟩
  have hidx : localIndex F (Function.Embedding.refl _) =
      localIndex P (Function.Embedding.refl _) := by
    rw [localIndex_preserves F P e he]
    exact localIndex_perm_all P (Function.Embedding.refl _) σ
  rw [hidx] at hsmall
  unfold centralIndex at hsmall hP
  omega

end Hypertournaments
