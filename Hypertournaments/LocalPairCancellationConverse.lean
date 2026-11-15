import Hypertournaments.LocalPairCancellation
import Hypertournaments.LocalBalancedPacket
import Hypertournaments.LocalConstantLink
import Hypertournaments.NormalizedPacketPermutation

/-!
# Exact pair-cancellation criterion for one local packet

The two central types admit a pair and an auxiliary order with constant
link. Combined with the constructive cutoff theorem, this proves the
full local-type equivalence, including arity three.
-/

namespace Hypertournaments

theorem localIndex_le_of_pairCancelling
    {n : ℕ} (hn : 3 ≤ n) (A : Hyper n (Fin (n + 1)))
    (hpc : PairCancelling A) :
    localIndex A (Function.Embedding.refl _) ≤ centralIndex n - 2 := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  by_contra hsmall
  have hlarge : k / 2 ≤ localIndex A (Function.Embedding.refl _) := by
    unfold centralIndex at hsmall
    omega
  let bits : Fin (k + 2) → Bool :=
    fun i => normalizedFacet A (Function.Embedding.refl _) i
  obtain ⟨σ, b, hσ⟩ := exists_perm_alternating_tail bits hlarge
  obtain ⟨c, hc⟩ := normalizedFacet_perm_up_to_complement A
    (Function.Embedding.refl _) σ
  let f : Fin (k + 2) ↪ Fin (k + 2) :=
    σ.toEmbedding.trans (Function.Embedding.refl _)
  have hraw (i : Fin k) :
      A.orient (facet f i.succ.succ) = Bool.xor c b := by
    have hh := hc i.succ.succ
    rw [show normalizedFacet A (Function.Embedding.refl _) (σ i.succ.succ) =
      bits (σ i.succ.succ) from rfl, hσ i] at hh
    have hm : i.succ.succ.val % 2 = i.val % 2 := by
      simp only [Fin.val_succ]
      omega
    change Bool.xor (A.orient (facet f i.succ.succ))
      (decide (i.succ.succ.val % 2 = 1)) =
        Bool.xor c (Bool.xor b (decide (i.val % 2 = 1))) at hh
    rw [hm] at hh
    cases hor : A.orient (facet f i.succ.succ) <;>
      cases c <;> cases b <;> cases hpar : decide (i.val % 2 = 1) <;>
      simp_all
  exact not_pairCancelling_of_constant_full_tail (by omega) A f
    σ.surjective (Bool.xor c b) hraw hpc

/-- On `n+1` vertices, the pair-cancelling local types are exactly those
below the two central indices. -/
theorem pairCancelling_iff_localIndex_le
    {n : ℕ} (hn : 3 ≤ n) (A : Hyper n (Fin (n + 1))) :
    PairCancelling A ↔
      localIndex A (Function.Embedding.refl _) ≤ centralIndex n - 2 :=
  ⟨localIndex_le_of_pairCancelling hn A, pairCancelling_of_localIndex_le hn A⟩

end Hypertournaments
