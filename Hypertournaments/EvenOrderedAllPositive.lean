import Lean.Elab.Tactic.Omega
import Hypertournaments.CanonicalPacket
import Hypertournaments.EvenAllPositivePacket

/-!
# All-positive ordered facet packets have the central local type

For an even arity 2k+2, an ordered packet on 2k+3 vertices
whose increasing facets all have positive raw orientation has exactly
the central minority index k+1. This bridges the previously certified
Boolean counting lemma with the *actual* intrinsic hypertournament
local-type API, on increasing tuples.

The extension from increasing tuples to arbitrary tuples still
requires an all-arity permutation-invariance theorem.
-/

namespace Hypertournaments

/-- A strictly increasing (2k+3)-tuple with every (2k+2)-facet
oriented positively has local type k+1. -/
theorem localIndex_ordered_allPositive_odd
    (k : ℕ) {V : Type*} [LinearOrder V]
    (signs : Finset V → Bool)
    (f : Fin (2 * k + 3) ↪o V)
    (h : ∀ i : Fin (2 * k + 3),
      signs (tupleVertices (facet f.toEmbedding i)) = true) :
    localIndex (Hyper.fromOrderedSigns (n := 2 * k + 2) signs)
      f.toEmbedding = k + 1 := by
  let D : Hyper (2 * k + 2) V :=
    Hyper.fromOrderedSigns signs
  have hfac (i : Fin (2 * k + 3)) :
      normalizedFacet D f.toEmbedding i =
        decide (i.val % 2 = 0) := by
    have hraw : D.orient (facet f.toEmbedding i) = true := by
      exact (fromOrderedSigns_facet_increasing signs f i).trans (h i)
    unfold normalizedFacet
    rw [hraw]
    by_cases hodd : i.val % 2 = 1
    · have heven : i.val % 2 ≠ 0 := by omega
      simp [hodd, heven]
    · have heven : i.val % 2 = 0 := by omega
      simp [hodd, heven]
  have hbits :
      (fun i : Fin (2 * k + 3) => normalizedFacet D f.toEmbedding i) =
      (fun i : Fin (2 * k + 3) => decide (i.val % 2 = 0)) := by
    funext i
    exact hfac i
  change
    min
      (boolPacketPositiveCount
        (fun i : Fin (2 * k + 3) =>
          normalizedFacet D f.toEmbedding i))
      ((2 * k + 3) -
        boolPacketPositiveCount
          (fun i : Fin (2 * k + 3) =>
            normalizedFacet D f.toEmbedding i)) =
      k + 1
  rw [hbits]
  exact boolPacketMinority_all_positive_odd k

end Hypertournaments
