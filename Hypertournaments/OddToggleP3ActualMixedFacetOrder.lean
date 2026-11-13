import Hypertournaments.OddToggleP3CanonicalMixedFacetOrder
import Hypertournaments.CanonicalPacket
import Hypertournaments.FinitePresentation

/-!
# Genuine intrinsic p3 mixed packet has the corrected facet order

The actual Boolean orientations on every facet of an increasing
(m+2)-vertex packet are the first m mixed facets, followed by
the facet deleting the left fresh point (right-side link beta),
then the facet deleting the right fresh point (left-side link
alpha). The first statement is a direct kernel-checked identity
of the real Hyper.orient table, not a synthetic packet.

When an actual canonical packet is alternating and m even, the
right endpoint beta equals the phase and the left endpoint alpha
is its complement. A separate pair of exact facet-set identities
identifies both endpoints with the true old-plus-fresh side sets.

No stochastic source or ordinary non-AP conclusion is asserted.
-/

namespace Hypertournaments

/-- The corrected mixed raw word is exactly the TRUE intrinsic
facet orientation word of any increasing actual hyperturnament
packet, with no assumptions on admissibility or gauge. -/
theorem Hyper.p3ActualMixedRawWord_eq
    (m a : ℕ) (E : Hyper (m+1) (Fin a))
    (f : Fin (m+2) ↪o Fin a) :
    p3CanonicalMixedRawWord m
      (fun i : Fin m =>
        E.orient (facet f.toEmbedding i.castSucc.castSucc))
      (E.orient (facet f.toEmbedding (Fin.last m).castSucc))
      (E.orient (facet f.toEmbedding (Fin.last (m+1)))) =
    (fun i : Fin (m+2) =>
      E.orient (facet f.toEmbedding i)) := by
  funext i
  rcases i.eq_castSucc_or_eq_last with ⟨j, rfl⟩ | rfl
  · rcases j.eq_castSucc_or_eq_last with ⟨k, rfl⟩ | rfl
    · exact p3CanonicalMixedRawWord_interior m
        (fun k : Fin m =>
          E.orient (facet f.toEmbedding k.castSucc.castSucc))
        _ _ k
    · exact p3CanonicalMixedRawWord_beta m
        (fun k : Fin m =>
          E.orient (facet f.toEmbedding k.castSucc.castSucc))
        _ _
  · exact p3CanonicalMixedRawWord_alpha m
      (fun k : Fin m =>
        E.orient (facet f.toEmbedding k.castSucc.castSucc))
      _ _

/-- An actual alternating canonical mixed packet has its
right-side beta endpoint equal to the phase and the left-side
alpha endpoint opposite to the phase, with no hidden reordering. -/
theorem Hyper.p3ActualMixedRawWord_alternating_endpoints
    (m a : ℕ) (hm : m % 2 = 0)
    (E : Hyper (m+1) (Fin a))
    (f : Fin (m+2) ↪o Fin a)
    (phase : Bool)
    (halt : (fun i : Fin (m+2) =>
      E.orient (facet f.toEmbedding i)) =
        p3AlternatingWord (m+2) phase) :
    E.orient (facet f.toEmbedding (Fin.last m).castSucc) = phase ∧
    E.orient (facet f.toEmbedding (Fin.last (m+1))) = !phase := by
  apply p3CanonicalMixedRawWord_alternating_endpoints m hm
    (fun i : Fin m =>
      E.orient (facet f.toEmbedding i.castSucc.castSucc))
    (E.orient (facet f.toEmbedding (Fin.last m).castSucc))
    (E.orient (facet f.toEmbedding (Fin.last (m+1))))
    phase
  exact (E.p3ActualMixedRawWord_eq m a f).trans halt

/-- Exact actual facet vertex sets for the two canonical
fresh endpoints. The second-to-last facet deletes left and
contains right; the final facet deletes right and contains left. -/
theorem p3CanonicalMixedEndpointFacet_sets
    (m a : ℕ) (f : Fin (m+2) ↪o Fin (a+2))
    (S : Finset (Fin (a+2))) (l r : Fin (a+2))
    (hlr : l ≠ r) (hlS : l ∉ S) (hrS : r ∉ S)
    (hvertices : tupleVertices f.toEmbedding = insert l (insert r S))
    (hleft : f (Fin.last m).castSucc = l)
    (hright : f (Fin.last (m+1)) = r) :
    tupleVertices (facet f.toEmbedding (Fin.last m).castSucc) =
      insert r S ∧
    tupleVertices (facet f.toEmbedding (Fin.last (m+1))) =
      insert l S := by
  constructor
  · rw [tupleVertices_facet_eq_erase f.toEmbedding
      ((Fin.last m).castSucc)]
    change (tupleVertices f.toEmbedding).erase
      (f ((Fin.last m).castSucc)) = insert r S
    rw [hleft, hvertices]
    ext z
    simp [hlr, hlS]
  · rw [tupleVertices_facet_eq_erase f.toEmbedding
      (Fin.last (m+1))]
    change (tupleVertices f.toEmbedding).erase
      (f (Fin.last (m+1))) = insert l S
    rw [hright, hvertices]
    ext z
    simp [hlr, hrS]

end Hypertournaments
