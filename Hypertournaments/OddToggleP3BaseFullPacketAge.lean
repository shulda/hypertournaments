import Hypertournaments.OddToggleP3AllOldFullBlockPair
import Hypertournaments.OddToggleP3SingletonErasure
import Hypertournaments.OddToggleP3AllOldMissingBlock
import Hypertournaments.OddToggleP3PotentialSwitching
import Hypertournaments.OddToggleP3ProtectedFacets

/-!
# Full-block old packets of the p3 random base are admissible

For m=4k+2≥6 and an old (m+2)-set U meeting all m blocks,
the exact six-block geometry gives two consecutive singleton labels
whose unique vertices have opposite canonical deletion parities.
Removing either vertex eliminates its block. The base W potential
is supported only on full transversals, so the corresponding
actual raw hypertournament facet orientation is zero.

The two opposite-parity zero facets exclude homogeneous local type,
while δ²=0 supplies switching parity. This establishes actual
exceptional-age membership for EVERY all-blocks-present packet
of the genuine W-induced base hypertournament.

This is the full-occupancy old-packet branch, without randomness.
The missing-block branch and the one-fresh side-packet branches
must be assembled separately for full p3 side admissibility.
-/

namespace Hypertournaments

/-- Any old finite set missing a full-transversal block has
zero F₂ coboundary of the base potential W. -/
theorem p3BasePotential_coboundary_zero_missing_block
    (m t : ℕ) (W : Finset (Fin (m*t)) → ZMod 2)
    (Q : Finset (Fin (m*t))) (i : Fin m)
    (hmissing : ∀ v ∈ Q, p3BlockNumber t v ≠ i.val) :
    coboundary (p3BasePotential m t W) Q = 0 := by
  unfold coboundary
  apply Finset.sum_eq_zero
  intro v hv
  apply p3BasePotential_zero_of_missing_block m t W (Q.erase v) i
  intro w hw
  exact hmissing w (Finset.mem_of_mem_erase hw)

/-- The actual canonical orientation of the old packet facet
erasing a singleton-block vertex equals zero. -/
theorem p3BaseHyper_raw_zero_at_singleton
    (m t : ℕ)
    (W : Finset (Fin (m*t)) → ZMod 2)
    (U : Finset (Fin (m*t))) (hU : U.card = m+2)
    (i : Fin m) (hi : p3BlockOccupancy m t U i = 1)
    (x : Fin (m+2))
    (hlabel : p3BlockNumber t (U.orderEmbOfFin hU x) = i.val) :
    (p3HyperFromPotential (m+1) (m*t) (p3BasePotential m t W)).orient
      (facet (U.orderEmbOfFin hU).toEmbedding x) = false := by
  let f : Fin (m+2) ↪o Fin (m*t) := U.orderEmbOfFin hU
  have hxU : f x ∈ U := by
    have himg : f x ∈ (Finset.univ : Finset (Fin (m+2))).image f :=
      Finset.mem_image_of_mem f (Finset.mem_univ x)
    simpa only [f, Finset.image_orderEmbOfFin_univ U hU] using himg
  have hmissing :
      ∀ v : Fin (m*t), v ∈ U.erase (f x) →
        p3BlockNumber t v ≠ i.val :=
    p3SingletonBlock_erase_missing m t U i hi (f x) hxU hlabel
  have hz :
      coboundary (p3BasePotential m t W) (U.erase (f x)) = 0 :=
    p3BasePotential_coboundary_zero_missing_block
      m t W (U.erase (f x)) i hmissing
  have hvertices :
      tupleVertices (facet f.toEmbedding x) = U.erase (f x) := by
    rw [tupleVertices_facet_eq_erase f.toEmbedding x]
    have hfvertices : tupleVertices f.toEmbedding = U := by
      dsimp [tupleVertices, f]
      exact Finset.image_orderEmbOfFin_univ U hU
    rw [hfvertices]
    rfl
  change (Hyper.fromOrderedSigns
    (p3PotentialSign (p3BasePotential m t W))).orient
      (facet f.toEmbedding x) = false
  rw [fromOrderedSigns_facet_increasing
    (p3PotentialSign (p3BasePotential m t W)) f x]
  rw [hvertices]
  simp [p3PotentialSign, p3ZMod2ToBool, hz]

/-- Every genuine full-block old packet with m+2 vertices
lies in the p3 exceptional homogeneous-free switching class. -/
theorem p3BaseFullOldPacket_allowed
    (k t : ℕ) (hk : 1 ≤ k) (ht : 0 < t)
    (W : Finset (Fin ((4*k+2)*t)) → ZMod 2)
    (U : Finset (Fin ((4*k+2)*t)))
    (hU : U.card = 4*k+4)
    (hall : ∀ i : Fin (4*k+2),
      0 < p3BlockOccupancy (4*k+2) t U i) :
    localIndex
      (p3HyperFromPotential (4*k+3) ((4*k+2)*t)
        (p3BasePotential (4*k+2) t W))
      (U.orderEmbOfFin hU).toEmbedding ∈
        toggleZero (switchingAllowed (4*k+3)) := by
  let A := p3HyperFromPotential (4*k+3) ((4*k+2)*t)
    (p3BasePotential (4*k+2) t W)
  let f : Fin (4*k+4) ↪o Fin ((4*k+2)*t) :=
    U.orderEmbOfFin hU
  have hm : 6 ≤ 4*k+2 := by omega
  obtain ⟨i,j,_,hi,hj,x,y,hx,hy,hpar⟩ :=
    p3AllOldFullBlocks_two_singletons_oppositeParity
      (4*k+2) t hm ht U hU hall
  have hrawx : A.orient (facet f.toEmbedding x) = false := by
    change (p3HyperFromPotential ((4*k+2)+1) ((4*k+2)*t)
      (p3BasePotential (4*k+2) t W)).orient
        (facet (U.orderEmbOfFin hU).toEmbedding x) = false
    exact p3BaseHyper_raw_zero_at_singleton
      (4*k+2) t W U hU i hi x hx
  have hrawy : A.orient (facet f.toEmbedding y) = false := by
    change (p3HyperFromPotential ((4*k+2)+1) ((4*k+2)*t)
      (p3BasePotential (4*k+2) t W)).orient
        (facet (U.orderEmbOfFin hU).toEmbedding y) = false
    exact p3BaseHyper_raw_zero_at_singleton
      (4*k+2) t W U hU j hj y hy
  have hnot : localIndex A f.toEmbedding ≠ 0 :=
    A.localIndex_ne_zero_of_oppositeParity_zeroRaw
      f x y hpar hrawx hrawy
  exact
    (p3HyperFromPotential_toggleAllowed_iff_nonhomogeneous
      k ((4*k+2)*t) (p3BasePotential (4*k+2) t W) f).mpr hnot

end Hypertournaments
