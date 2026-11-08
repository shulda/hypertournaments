import Hypertournaments.LocalTypeInvariantFour
import Hypertournaments.DirectCertificateBridge

/-!
# From canonical five-sets to ordinary admissibility

Every injective five-tuple is a reordering of the unique increasing
enumeration of its image. Consequently, arity-four local-type
permutation invariance upgrades the canonical finite sign-table
certificates to full admissibility (all injective five-tuples).

The proof is independent of the particular seven-vertex seed.
-/

namespace Hypertournaments

/-- A 4-hypertournament is central-only if and only if its
canonical increasing five-tuples all have central local type. -/
theorem admissible_four_of_canonical
    {k : ℕ} (A : Hyper 4 (Fin k))
    (h : ∀ Q : Finset (Fin k), canonicalCentral4At A Q) :
    Admissible ({2} : Set ℕ) A := by
  intro f
  change localIndex A f = 2
  let Q : Finset (Fin k) := tupleVertices f
  have hQ : Q.card = 5 := by
    dsimp [Q, tupleVertices]
    rw [Finset.card_image_of_injective _ f.injective]
    simp
  let g : Fin 5 ↪o Fin k := Q.orderEmbOfFin hQ
  let τ : Equiv.Perm (Fin 5) := Tuple.sort (f : Fin 5 → Fin k)
  have hmono : Monotone ((f : Fin 5 → Fin k) ∘ τ) :=
    Tuple.monotone_sort (f : Fin 5 → Fin k)
  have hinj : Function.Injective ((f : Fin 5 → Fin k) ∘ τ) :=
    f.injective.comp τ.injective
  have hsorted : (f : Fin 5 → Fin k) ∘ τ = (g : Fin 5 → Fin k) := by
    exact Finset.orderEmbOfFin_unique hQ (by
      intro i
      change f (τ i) ∈ Q
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)) 
      (hmono.strictMono_of_injective hinj)
  have hreorder : τ.symm.toEmbedding.trans g.toEmbedding = f := by
    ext x
    have hx := congrFun hsorted (τ.symm x)
    simpa [Function.comp_apply] using hx.symm
  have hg : localIndex A g.toEmbedding = 2 := by
    have hh := h Q
    simpa [canonicalCentral4At, hQ, g] using hh
  calc
    localIndex A f =
        localIndex A (τ.symm.toEmbedding.trans g.toEmbedding) := by rw [hreorder]
    _ = localIndex A g.toEmbedding := localIndex_perm4 A g.toEmbedding τ.symm
    _ = 2 := hg

/-- The seven-vertex base of the explicit central-only witness is
admissible in the *ordinary* un-ordered four-hypertournament age. -/
theorem seed4_base_admissible :
    Admissible ({2} : Set ℕ) seed4Base :=
  admissible_four_of_canonical seed4Base seed4_base_canonicalCentral

theorem seed4_left_admissible :
    Admissible ({2} : Set ℕ) seed4Left :=
  admissible_four_of_canonical seed4Left seed4_left_canonicalCentral

theorem seed4_right_admissible :
    Admissible ({2} : Set ℕ) seed4Right :=
  admissible_four_of_canonical seed4Right seed4_right_canonicalCentral

end Hypertournaments
