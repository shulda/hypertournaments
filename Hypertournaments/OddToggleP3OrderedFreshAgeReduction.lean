import Mathlib.Tactic.Ext
import Hypertournaments.OddToggleP3CanonicalSideAgeReduction
import Hypertournaments.AllArityCanonicalAdmissibility

/-!
# To prove actual p3 one-point side age, only increasing fresh packets matter

The existing one-point age reduction checks ALL injective (m+2)-tuples
containing the fresh vertex. The local index of an intrinsic
hypertournament is permutation-invariant, and every such tuple has
a unique increasing enumeration of the same vertex set.

Hence it is enough to check actual canonical increasing packets
with the new point. This is the exact reduction needed to compose
the three occupancy branches q≤m−2, q=m−1, q=m.
The auxiliary order is not an expansion of the language.
-/

namespace Hypertournaments

/-- Checking fresh-containing packets with their increasing
enumeration suffices for complete intrinsic age membership
of the canonical one-point p3 side, because the old base is
already known to be admissible for arbitrary W. -/
theorem p3CanonicalSide_admissible_of_ordered_fresh_packets
    (k t : ℕ) (hk : 1 ≤ k) (ht : 0 < t)
    (eligible : Finset (Fin (4*k+2)))
    (W L : Finset (Fin ((4*k+2)*t)) → ZMod 2)
    (hnew : ∀ f : Fin (((4*k+2)+1)+1) ↪o Fin ((4*k+2)*t+1),
      Fin.last ((4*k+2)*t) ∈ tupleVertices f.toEmbedding →
      localIndex (p3CanonicalSide (4*k+2) t eligible W L)
        f.toEmbedding ∈
          toggleZero (switchingAllowed (4*k+3))) :
    Admissible (toggleZero (switchingAllowed (4*k+3)))
      (p3CanonicalSide (4*k+2) t eligible W L) := by
  let A := p3CanonicalSide (4*k+2) t eligible W L
  apply p3CanonicalSide_admissible_of_fresh_packets
    k t hk ht eligible W L
  intro f hf
  let Q := tupleVertices f
  have hQ : Q.card = (((4*k+2)+1)+1) := by
    dsimp [Q,tupleVertices]
    rw [Finset.card_image_of_injective _ f.injective]
    simp
  let g : Fin (((4*k+2)+1)+1) ↪o Fin ((4*k+2)*t+1) :=
    Q.orderEmbOfFin hQ
  have hfreshG : Fin.last ((4*k+2)*t) ∈
      tupleVertices g.toEmbedding := by
    change Fin.last ((4*k+2)*t) ∈
      (Finset.univ : Finset (Fin (((4*k+2)+1)+1))).image g
    rw [Finset.image_orderEmbOfFin_univ Q hQ]
    exact hf
  let τ : Equiv.Perm (Fin (((4*k+2)+1)+1)) :=
    Tuple.sort (f : Fin (((4*k+2)+1)+1) → Fin ((4*k+2)*t+1))
  have hmono : Monotone
      ((f : Fin (((4*k+2)+1)+1) → Fin ((4*k+2)*t+1)) ∘ τ) :=
    Tuple.monotone_sort (f : Fin (((4*k+2)+1)+1) → Fin ((4*k+2)*t+1))
  have hinj : Function.Injective
      ((f : Fin (((4*k+2)+1)+1) → Fin ((4*k+2)*t+1)) ∘ τ) :=
    f.injective.comp τ.injective
  have hsorted :
      (f : Fin (((4*k+2)+1)+1) → Fin ((4*k+2)*t+1)) ∘ τ =
      (g : Fin (((4*k+2)+1)+1) → Fin ((4*k+2)*t+1)) := by
    exact Finset.orderEmbOfFin_unique hQ
      (by
        intro i
        change f (τ i) ∈ Q
        exact Finset.mem_image_of_mem _ (Finset.mem_univ _))
      (hmono.strictMono_of_injective hinj)
  have hemb : τ.toEmbedding.trans f = g.toEmbedding := by
    ext i
    exact congrArg Fin.val (congrFun hsorted i)
  have hlocal := localIndex_perm_all A f τ
  rw [hemb] at hlocal
  rw [← hlocal]
  exact hnew g hfreshG

end Hypertournaments
