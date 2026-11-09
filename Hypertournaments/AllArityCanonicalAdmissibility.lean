import Hypertournaments.GeneralLocalIndexInvariant
import Hypertournaments.CanonicalPacket

/-!
# All-arity canonical-subset admissibility certificate

The all-arity invariance theorem localIndex_perm_all identifies the
local type of any injective (n+1)-tuple with its increasing sorted
reordering. Therefore one can certify membership in an age by checking
the unique increasing enumeration of each actual (n+1)-element subset.
This result is strictly about the intrinsic hypertournament language;
the chosen order on Fin k is not added to the structure.
-/

namespace Hypertournaments

/-- Uniformly in all arities, admissibility is equivalent to
checking local type membership only on increasing enumerations. -/
theorem admissible_iff_canonical_all
    {n k : ℕ} (S : Set ℕ) (A : Hyper n (Fin k)) :
    Admissible S A ↔
      ∀ Q : Finset (Fin k), ∀ hQ : Q.card = n + 1,
        localIndex A (Q.orderEmbOfFin hQ).toEmbedding ∈ S := by
  constructor
  · intro h Q hQ
    exact h (Q.orderEmbOfFin hQ).toEmbedding
  · intro h f
    let Q : Finset (Fin k) := tupleVertices f
    have hQ : Q.card = n + 1 := by
      dsimp [Q, tupleVertices]
      rw [Finset.card_image_of_injective _ f.injective]
      simp
    let g : Fin (n + 1) ↪o Fin k := Q.orderEmbOfFin hQ
    let τ : Equiv.Perm (Fin (n + 1)) :=
      Tuple.sort (f : Fin (n + 1) → Fin k)
    have hmono :
        Monotone ((f : Fin (n + 1) → Fin k) ∘ τ) :=
      Tuple.monotone_sort (f : Fin (n + 1) → Fin k)
    have hinj :
        Function.Injective ((f : Fin (n + 1) → Fin k) ∘ τ) :=
      f.injective.comp τ.injective
    have hsorted :
        (f : Fin (n + 1) → Fin k) ∘ τ =
          (g : Fin (n + 1) → Fin k) := by
      exact Finset.orderEmbOfFin_unique hQ
        (by
          intro i
          change f (τ i) ∈ Q
          exact Finset.mem_image_of_mem _ (Finset.mem_univ _))
        (hmono.strictMono_of_injective hinj)
    have hemb : τ.toEmbedding.trans f = g.toEmbedding := by
      ext i
      exact congrFun hsorted i
    have hlocal := localIndex_perm_all A f τ
    rw [hemb] at hlocal
    rw [← hlocal]
    exact h Q hQ

end Hypertournaments
