import Hypertournaments.FacetOrientationRecovery
import Hypertournaments.LocalBalancedPacket
import Hypertournaments.NormalizedPacketSign
import Hypertournaments.OnePointNonmixedAdmissible

/-!
# Local indices classify the actual local isomorphism types

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`lem:local-type-isomorphism` in the proof preparation.

Equal minority counts match normalized packets up to a complement. On at
least three entries, a transposition inside a color class can correct the
permutation parity without changing that matching. The exact sign law then
matches all actual facets and recovers an orientation-preserving vertex
equivalence.
-/

namespace Hypertournaments

/-- A Boolean packet with at least three entries has two equally colored
distinct entries. -/
theorem exists_boolPacket_equal_pair {m : ℕ} (hm : 3 ≤ m)
    (bits : Fin m → Bool) : ∃ i j : Fin m, i ≠ j ∧ bits i = bits j := by
  classical
  by_contra h
  have hinj : Function.Injective bits := by
    intro i j hij
    by_contra hne
    exact h ⟨i, j, hne, hij⟩
  have hc := Fintype.card_le_of_injective bits hinj
  simp only [Fintype.card_fin, Fintype.card_bool] at hc
  omega

/-- Any matching of Boolean color classes on at least three entries can
be chosen with either prescribed permutation parity. -/
theorem exists_boolPacket_permutation_with_signBit {m : ℕ}
    (bits target : Fin m → Bool) (hm : 3 ≤ m)
    (hcount : boolPacketPositiveCount target = boolPacketPositiveCount bits)
    (parity : Bool) :
    ∃ σ : Equiv.Perm (Fin m), permutationSignBit σ = parity ∧
      ∀ i, bits (σ i) = target i := by
  classical
  obtain ⟨σ, hσ⟩ := exists_boolPacket_permutation_of_count_eq bits target hcount
  by_cases hp : permutationSignBit σ = parity
  · exact ⟨σ, hp, hσ⟩
  obtain ⟨a, b, hab, hcolor⟩ := exists_boolPacket_equal_pair hm target
  have hfix (i : Fin m) : target (Equiv.swap a b i) = target i := by
    by_cases ha : i = a
    · subst i
      rw [Equiv.swap_apply_left]
      exact hcolor.symm
    by_cases hb : i = b
    · subst i
      rw [Equiv.swap_apply_right]
      exact hcolor
    rw [Equiv.swap_apply_of_ne_of_ne ha hb]
  refine ⟨σ * Equiv.swap a b, ?_, ?_⟩
  · rw [permutationSignBit_mul, permutationSignBit_swap a b hab]
    cases hs : permutationSignBit σ <;> cases parity <;> simp_all
  · intro i
    change bits (σ (Equiv.swap a b i)) = target i
    exact (hσ (Equiv.swap a b i)).trans (hfix i)

/-- Equality of minority counts gives an actual signed permutation of the
whole packets, with its complement equal to the permutation's own parity. -/
theorem exists_boolPacket_signed_permutation_of_minority_eq {m : ℕ}
    (bits target : Fin m → Bool) (hm : 3 ≤ m)
    (hminority :
      min (boolPacketPositiveCount target) (m - boolPacketPositiveCount target) =
        min (boolPacketPositiveCount bits) (m - boolPacketPositiveCount bits)) :
    ∃ σ : Equiv.Perm (Fin m), ∀ i,
      Bool.xor (permutationSignBit σ) (bits (σ i)) = target i := by
  have hb := boolPacketPositiveCount_le bits
  have ht := boolPacketPositiveCount_le target
  have hcounts : boolPacketPositiveCount target = boolPacketPositiveCount bits ∨
      boolPacketPositiveCount target = m - boolPacketPositiveCount bits := by
    omega
  have hc : ∃ c : Bool,
      boolPacketPositiveCount (fun i => Bool.xor c (target i)) =
        boolPacketPositiveCount bits := by
    rcases hcounts with h | h
    · exact ⟨false, by simpa using h⟩
    · refine ⟨true, ?_⟩
      have heq : (fun i => Bool.xor true (target i)) = (fun i => !(target i)) := by
        funext i
        cases target i <;> rfl
      rw [heq, boolPacketPositiveCount_not]
      omega
  obtain ⟨c, hc⟩ := hc
  obtain ⟨σ, hp, hσ⟩ := exists_boolPacket_permutation_with_signBit
    bits (fun i => Bool.xor c (target i)) hm hc c
  refine ⟨σ, ?_⟩
  intro i
  rw [hp, hσ]
  cases c <;> cases target i <;> rfl

/-- Equal local indices yield an actual orientation-preserving vertex
equivalence, uniformly in every arity at least two. -/
theorem exists_preserving_perm_of_localIndex_eq {n : ℕ} (hn : 2 ≤ n)
    (A B : Hyper n (Fin (n + 1)))
    (hindex : localIndex A (Function.Embedding.refl _) =
      localIndex B (Function.Embedding.refl _)) :
    ∃ σ : Equiv.Perm (Fin (n + 1)), Preserves A B σ.toEmbedding := by
  let a : Fin (n + 1) → Bool := normalizedFacet A (Function.Embedding.refl _)
  let b : Fin (n + 1) → Bool := normalizedFacet B (Function.Embedding.refl _)
  have hminority :
      min (boolPacketPositiveCount a) ((n + 1) - boolPacketPositiveCount a) =
        min (boolPacketPositiveCount b) ((n + 1) - boolPacketPositiveCount b) := hindex
  obtain ⟨σ, hσ⟩ := exists_boolPacket_signed_permutation_of_minority_eq b a (by omega) hminority
  refine ⟨σ, preserves_of_normalizedFacets A B σ.toEmbedding ?_⟩
  intro i
  have ht : σ.toEmbedding.trans (Function.Embedding.refl _) = σ.toEmbedding := by
    ext j
    rfl
  have h := (normalizedFacet_perm_signBit B (Function.Embedding.refl _) σ i).trans (hσ i)
  simpa only [ht] using h

/-- The local index is a complete invariant for actual isomorphisms of
n-hypertournaments on n+1 vertices. No orientation or order is forgotten. -/
theorem localIndex_eq_iff_exists_preserving_perm {n : ℕ} (hn : 2 ≤ n)
    (A B : Hyper n (Fin (n + 1))) :
    localIndex A (Function.Embedding.refl _) =
        localIndex B (Function.Embedding.refl _) ↔
      ∃ σ : Equiv.Perm (Fin (n + 1)), Preserves A B σ.toEmbedding := by
  constructor
  · exact exists_preserving_perm_of_localIndex_eq hn A B
  · rintro ⟨σ, hσ⟩
    have h := localIndex_preserves A B σ.toEmbedding hσ (Function.Embedding.refl _)
    have h₁ : (Function.Embedding.refl _).trans σ.toEmbedding = σ.toEmbedding := by
      ext i
      rfl
    have h₂ : σ.toEmbedding.trans (Function.Embedding.refl _) = σ.toEmbedding := by
      ext i
      rfl
    have hp := localIndex_perm_all B (Function.Embedding.refl _) σ
    rw [h₁] at h
    rw [h₂] at hp
    exact h.trans hp

end Hypertournaments
