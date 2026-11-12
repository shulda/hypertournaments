import Hypertournaments.OddToggleP3BaseFullPacketAge
import Hypertournaments.OddToggleP3AllZeroRawType
import Hypertournaments.AllArityCanonicalAdmissibility

/-!
# Full admissibility of the potential-induced old p3 base

For every k≥1 (arity n=4k+3≥7) and every positive block size t,
the common old hypertournament generated from an arbitrary
full-transversal potential W is genuinely in the exceptional
homogeneous-free switching age, for EVERY choice of W.

Every old (m+2)-set Q, m=4k+2, has one of two exhaustive cases:
  - some old block is missing: every raw facet orientation is zero,
    so its local type is central and is permitted;
  - all m blocks occur: exact occupancy excess + six-block singleton
    selection + canonical sorted position parity yields two genuine
    zero raw facets at opposite parities, excluding type zero, and
    potential-induced switching parity supplies the other constraint.

The result is actual intrinsic Hyper admissibility for all injective
tuples by the already certified all-arity canonical admissibility
equivalence. This does NOT assert the two one-point sides are
admissible; the packets containing a fresh vertex remain to analyze.
-/

namespace Hypertournaments

/-- If any full-transversal old block is absent, every raw facet
of the genuine W-potential-induced old hyperturnament packet is zero. -/
theorem p3BaseOldPacket_allRawZero_of_missing_block
    (k t : ℕ)
    (W : Finset (Fin ((4*k+2)*t)) → ZMod 2)
    (Q : Finset (Fin ((4*k+2)*t)))
    (hQ : Q.card = 4*k+4) (i : Fin (4*k+2))
    (hmissing : ∀ v ∈ Q, p3BlockNumber t v ≠ i.val) :
    ∀ q : Fin (4*k+4),
      (p3HyperFromPotential (4*k+3) ((4*k+2)*t)
        (p3BasePotential (4*k+2) t W)).orient
        (facet (Q.orderEmbOfFin hQ).toEmbedding q) = false := by
  let f : Fin (4*k+4) ↪o Fin ((4*k+2)*t) := Q.orderEmbOfFin hQ
  intro q
  have hvertices :
      tupleVertices (facet f.toEmbedding q) = Q.erase (f q) := by
    rw [tupleVertices_facet_eq_erase f.toEmbedding q]
    have hf : tupleVertices f.toEmbedding = Q := by
      dsimp [tupleVertices, f]
      exact Finset.image_orderEmbOfFin_univ Q hQ
    rw [hf]
  have hmissing' :
      ∀ v ∈ Q.erase (f q), p3BlockNumber t v ≠ i.val := by
    intro v hv
    exact hmissing v (Finset.mem_of_mem_erase hv)
  have hz :
      coboundary (p3BasePotential (4*k+2) t W)
        (Q.erase (f q)) = 0 :=
    p3BasePotential_coboundary_zero_missing_block
      (4*k+2) t W (Q.erase (f q)) i hmissing'
  change (Hyper.fromOrderedSigns
    (p3PotentialSign (p3BasePotential (4*k+2) t W))).orient
      (facet f.toEmbedding q) = false
  rw [fromOrderedSigns_facet_increasing
    (p3PotentialSign (p3BasePotential (4*k+2) t W)) f q]
  rw [hvertices]
  simp [p3PotentialSign, p3ZMod2ToBool, hz]

/-- Every old p3 packet missing a block belongs to the exceptional
age; in fact its exact local type is central. -/
theorem p3BaseOldPacket_allowed_of_missing_block
    (k t : ℕ)
    (W : Finset (Fin ((4*k+2)*t)) → ZMod 2)
    (Q : Finset (Fin ((4*k+2)*t)))
    (hQ : Q.card = 4*k+4) (i : Fin (4*k+2))
    (hmissing : ∀ v ∈ Q, p3BlockNumber t v ≠ i.val) :
    localIndex
      (p3HyperFromPotential (4*k+3) ((4*k+2)*t)
        (p3BasePotential (4*k+2) t W))
      (Q.orderEmbOfFin hQ).toEmbedding ∈
        toggleZero (switchingAllowed (4*k+3)) := by
  apply Hyper.p3ToggleAllowed_of_all_raw_zero k
    (p3HyperFromPotential (4*k+3) ((4*k+2)*t)
      (p3BasePotential (4*k+2) t W))
    (Q.orderEmbOfFin hQ).toEmbedding
  exact p3BaseOldPacket_allRawZero_of_missing_block
    k t W Q hQ i hmissing

/-- The genuine common W-induced old base structure is
unconditionally admitted by the exceptional p3 class, for all
arbitrary W, all k≥1 and positive block size t. -/
theorem p3BaseHyper_admissible
    (k t : ℕ) (hk : 1 ≤ k) (ht : 0 < t)
    (W : Finset (Fin ((4*k+2)*t)) → ZMod 2) :
    Admissible (toggleZero (switchingAllowed (4*k+3)))
      (p3HyperFromPotential (4*k+3) ((4*k+2)*t)
        (p3BasePotential (4*k+2) t W)) := by
  classical
  apply (admissible_iff_canonical_all
    (toggleZero (switchingAllowed (4*k+3)))
    (p3HyperFromPotential (4*k+3) ((4*k+2)*t)
      (p3BasePotential (4*k+2) t W))).mpr
  intro Q hQ
  have hcard : Q.card = 4*k+4 := by omega
  by_cases hall : ∀ i : Fin (4*k+2),
      0 < p3BlockOccupancy (4*k+2) t Q i
  · have hallowed :=
      p3BaseFullOldPacket_allowed k t hk ht W Q hcard hall
    simpa only [show 4*k+3+1=4*k+4 by omega] using hallowed
  · push_neg at hall
    obtain ⟨i, hi⟩ := hall
    have hzero : p3BlockOccupancy (4*k+2) t Q i = 0 := by omega
    have hfilter :
        Q.filter (fun v => p3BlockNumber t v = i.val) = ∅ := by
      exact Finset.card_eq_zero.mp (show
        (Q.filter (fun v => p3BlockNumber t v = i.val)).card = 0
        from hzero)
    have hmissing : ∀ v ∈ Q, p3BlockNumber t v ≠ i.val := by
      intro v hv heq
      have hmem : v ∈ Q.filter
          (fun w => p3BlockNumber t w = i.val) :=
        Finset.mem_filter.mpr ⟨hv, heq⟩
      rw [hfilter] at hmem
      simpa using hmem
    have hallowed :=
      p3BaseOldPacket_allowed_of_missing_block
        k t W Q hcard i hmissing
    simpa only [show 4*k+3+1=4*k+4 by omega] using hallowed

end Hypertournaments
