import Hypertournaments.RootedOddSuspensionSigns
import Hypertournaments.EvenSuspensionAllTwoPadPackets
import Hypertournaments.EvenSuspensionOrderedFacets
import Hypertournaments.CanonicalPacket

/-!
# The rooted odd h=2 packet is identical to the unrooted even h=2 packet

The rooted odd and unrooted even suspensions have exactly the same
signs on all high subsets with two pads, and they both assign
positive signs to high subsets with exactly one pad. Thus their
facet orientations agree on every increasing high packet with
exactly two pads, despite differing elsewhere (at three pads).

Using the previously kernel-checked all-arity unrooted two-pad
type shift, we obtain the exact +1 old local-type formula for
all rooted odd two-pad increasing packets. The root location is
irrelevant for this case.
-/

namespace Hypertournaments

/-- The local index of a particular tuple is determined by the raw
orientations of its facets, not any other orientation values. -/
theorem localIndex_eq_of_facet_orient_eq
    {n : ℕ} {V : Type*}
    (A B : Hyper n V) (f : Fin (n+1) ↪ V)
    (h : ∀ i : Fin (n+1),
      A.orient (facet f i) = B.orient (facet f i)) :
    localIndex A f = localIndex B f := by
  have hc : positiveFacetCount A f = positiveFacetCount B f := by
    unfold positiveFacetCount
    apply congrArg Finset.card
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold normalizedFacet
    rw [h i]
  unfold localIndex
  rw [hc]

/-- Erasing any vertex from a two-pad parent cannot produce a
three-pad facet. -/
theorem rootedOdd_two_pad_facet_ne_three
    (m a : ℕ) (Q : Finset (Fin (m+a)))
    (h2 : (evenPadProjection m a Q).card = 2)
    (v : Fin (m+a)) :
    (evenPadProjection m a (Q.erase v)).card ≠ 3 := by
  have h := evenPadProjection_erase_card m a Q v
  rcases h with h | h <;> omega

/-- For an increasing packet with exactly two pads the two
suspensions have exactly the same *actual* raw facet orientations. -/
theorem Hyper.rootedOddSuspension_facets_eq_even_of_twoPads
    {n m a : ℕ} (A : Hyper n (Fin a))
    (root : Fin a)
    (f : Fin (n+3) ↪o Fin (m+a))
    (h2 : (evenPadProjection m a (tupleVertices f.toEmbedding)).card = 2)
    (i : Fin (n+3)) :
    (A.rootedOddSuspension m a root).orient (facet f.toEmbedding i) =
      (A.evenSuspension m a).orient (facet f.toEmbedding i) := by
  let Q : Finset (Fin (m+a)) :=
    tupleVertices (facet f.toEmbedding i)
  have hne : (evenPadProjection m a Q).card ≠ 3 := by
    change (evenPadProjection m a
      (tupleVertices (facet f.toEmbedding i))).card ≠ 3
    rw [tupleVertices_facet_eq_erase]
    exact rootedOdd_two_pad_facet_ne_three m a
      (tupleVertices f.toEmbedding) h2 (f i)
  calc
    (A.rootedOddSuspension m a root).orient (facet f.toEmbedding i) =
      rootedOddSuspensionSignTable m a A root Q :=
        fromOrderedSigns_facet_increasing
          (rootedOddSuspensionSignTable m a A root) f i
    _ = evenSuspensionSignTable m a A Q := by
      unfold rootedOddSuspensionSignTable evenSuspensionSignTable
      by_cases hh : (evenPadProjection m a Q).card = 2
      · simp [hh]
      · simp [hh, hne]
    _ = (A.evenSuspension m a).orient (facet f.toEmbedding i) :=
        (fromOrderedSigns_facet_increasing
          (evenSuspensionSignTable m a A) f i).symm

/-- Every increasing rooted odd two-pad packet has old local type
raised by exactly one, independent of the distinguished root. -/
theorem Hyper.rootedOddSuspension_localIndex_increasing_twoPads
    {n : ℕ} (m a : ℕ) (A : Hyper n (Fin a))
    (root : Fin a)
    (f : Fin (n+3) ↪o Fin (m+a))
    (h2 : (evenPadProjection m a (tupleVertices f.toEmbedding)).card = 2) :
    ∃ t : Fin (n+1) ↪o Fin a,
      localIndex (A.rootedOddSuspension m a root) f.toEmbedding =
        localIndex A t.toEmbedding + 1 := by
  have heq :
      localIndex (A.rootedOddSuspension m a root) f.toEmbedding =
      localIndex (A.evenSuspension m a) f.toEmbedding := by
    apply localIndex_eq_of_facet_orient_eq
    intro i
    exact A.rootedOddSuspension_facets_eq_even_of_twoPads
      root f h2 i
  obtain ⟨t, ht⟩ :=
    A.evenSuspension_localIndex_increasing_twoPads m a f h2
  exact ⟨t, heq.trans ht⟩

end Hypertournaments
