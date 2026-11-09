import Hypertournaments.EvenSuspensionOrderedFacets
import Hypertournaments.EvenOrderedAllPositive

/-!
# Central local index of increasing suspension packets outside h=2,3

This theorem brings together three independent pieces:
* the concrete even suspension's sign table,
* actual orientation-level facet positivity for pad counts <=1 or >=4,
* the general odd-length Boolean packet minority count.

For even source arity n=2k, every increasing high (n+3)-tuple
with 0, 1, or >=4 pads has exact central local type k+1.
The all-arity permutation-invariance theorem is still needed to
conclude the corresponding claim for arbitrary tuple orderings.
-/

namespace Hypertournaments

theorem Hyper.evenSuspension_localIndex_increasing_far
    (k m a : ℕ)
    (A : Hyper (2 * k) (Fin a))
    (f : Fin (2 * k + 3) ↪o Fin (m + a))
    (hcount :
      (evenPadProjection m a (tupleVertices f.toEmbedding)).card ≤ 1 ∨
      4 ≤ (evenPadProjection m a (tupleVertices f.toEmbedding)).card) :
    localIndex (A.evenSuspension m a) f.toEmbedding = k + 1 := by
  have htable :
      ∀ i : Fin (2 * k + 3),
        evenSuspensionSignTable m a A
          (tupleVertices (facet f.toEmbedding i)) = true := by
    intro i
    have hraw :=
      A.evenSuspension_orient_increasingFacet_far f hcount i
    have hread :=
      fromOrderedSigns_facet_increasing
        (evenSuspensionSignTable m a A) f i
    exact hread.symm.trans hraw
  exact localIndex_ordered_allPositive_odd k
    (evenSuspensionSignTable m a A) f htable

end Hypertournaments
