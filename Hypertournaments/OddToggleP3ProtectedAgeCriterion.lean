import Hypertournaments.OddToggleP3ProtectedCoverage
import Hypertournaments.OddToggleP3ProtectedFacets
import Hypertournaments.OddToggleP3AgeSplit
import Hypertournaments.AllArityCanonicalAdmissibility

/-!
# Exact sufficient support geometry for full p3 side admissibility

A potential z may be arbitrary on its permitted support. Suppose all
nonzero potential entries meet each label in a protectedBlocks block family.
If EVERY canonical (4k+4)-packet has two protectedBlocks singleton blocks
whose vertices occupy positions of opposite deletion parity, then
each of those two facets has raw sign zero. Therefore the actual
potential-induced intrinsic Hyper (4k+3) contains no homogeneous
packet. Switching parity holds automatically by δδ=0, so the full
exceptional toggleZero age condition follows.

This criterion is conditional on the explicit block-pair geometry.
For packets missing a protectedBlocks block, the existing missing-block
zero-facet lemma will allow a different later geometry certificate.
This file does NOT assert that the concrete random p3 sides already
satisfy the stated geometry in every packet.
-/

namespace Hypertournaments

/-- Two protectedBlocks singleton blocks in opposite parity positions
give a genuine exceptional-age local packet of the potential-induced
intrinsic hypertournament. -/
theorem p3PotentialPacket_allowed_of_protected_pair
    (k a : ℕ) {I : Type*}
    (block : Fin a → I) (protectedBlocks : Finset I)
    (z : Finset (Fin a) → ZMod 2)
    (hcover : p3PotentialCoversBlocks block protectedBlocks z)
    (f : Fin (4*k+4) ↪o Fin a)
    (i j : Fin (4*k+4))
    (hpar : decide (i.val%2=1) ≠ decide (j.val%2=1))
    (hip : block (f i) ∈ protectedBlocks)
    (hjp : block (f j) ∈ protectedBlocks)
    (huniquei : ∀ q : Fin (4*k+4),
      block (f q) = block (f i) → q = i)
    (huniquej : ∀ q : Fin (4*k+4),
      block (f q) = block (f j) → q = j) :
    localIndex (p3HyperFromPotential (4*k+3) a z)
        f.toEmbedding ∈ toggleZero (switchingAllowed (4*k+3)) := by
  have hiZ : p3PotentialSign z
      (tupleVertices (facet f.toEmbedding i)) = false :=
    p3PotentialSign_zero_on_unique_packet_block
      block protectedBlocks z hcover f i hip huniquei
  have hjZ : p3PotentialSign z
      (tupleVertices (facet f.toEmbedding j)) = false :=
    p3PotentialSign_zero_on_unique_packet_block
      block protectedBlocks z hcover f j hjp huniquej
  have hiCard : (tupleVertices (facet f.toEmbedding i)).card = 4*k+3 := by
    dsimp [tupleVertices]
    rw [Finset.card_image_of_injective _ (facet f.toEmbedding i).injective]
    simp
  have hjCard : (tupleVertices (facet f.toEmbedding j)).card = 4*k+3 := by
    dsimp [tupleVertices]
    rw [Finset.card_image_of_injective _ (facet f.toEmbedding j).injective]
    simp
  have hiCanon : (p3HyperFromPotential (4*k+3) a z).canonicalSignTable
      (tupleVertices (facet f.toEmbedding i)) = false := by
    rw [p3HyperFromPotential_canonical (4*k+3) a z _ hiCard]
    exact hiZ
  have hjCanon : (p3HyperFromPotential (4*k+3) a z).canonicalSignTable
      (tupleVertices (facet f.toEmbedding j)) = false := by
    rw [p3HyperFromPotential_canonical (4*k+3) a z _ hjCard]
    exact hjZ
  have hnot : localIndex (p3HyperFromPotential (4*k+3) a z)
        f.toEmbedding ≠ 0 :=
    Hyper.localIndex_ne_zero_of_oppositeParity_zeroCanonical
      (p3HyperFromPotential (4*k+3) a z) f i j hpar hiCanon hjCanon
  exact (Hyper.p3ToggleAllowed_iff_coboundary_zero_and_nonhomogeneous
    k a (p3HyperFromPotential (4*k+3) a z) f).mpr
    ⟨p3HyperFromPotential_rawCoboundary_zero (4*k+3) a z f, hnot⟩

/-- A purely finite block-support hypothesis and the existence
of opposite-parity singleton protectedBlocks blocks in EVERY canonical
packet suffice for full intrinsic age membership, including all
unordered/reordered injective tuples. -/
theorem p3PotentialHyper_admissible_of_protected_pairs
    (k a : ℕ) {I : Type*}
    (block : Fin a → I) (protectedBlocks : Finset I)
    (z : Finset (Fin a) → ZMod 2)
    (hcover : p3PotentialCoversBlocks block protectedBlocks z)
    (hgeometry : ∀ f : Fin (4*k+4) ↪o Fin a,
      ∃ i j : Fin (4*k+4),
        decide (i.val%2=1) ≠ decide (j.val%2=1) ∧
        block (f i) ∈ protectedBlocks ∧ block (f j) ∈ protectedBlocks ∧
        (∀ q : Fin (4*k+4),
          block (f q) = block (f i) → q = i) ∧
        (∀ q : Fin (4*k+4),
          block (f q) = block (f j) → q = j)) :
    Admissible (toggleZero (switchingAllowed (4*k+3)))
      (p3HyperFromPotential (4*k+3) a z) := by
  apply (admissible_iff_canonical_all
    (toggleZero (switchingAllowed (4*k+3)))
    (p3HyperFromPotential (4*k+3) a z)).mpr
  intro Q hQ
  have hQ' : Q.card = 4*k+4 := by omega
  let f : Fin (4*k+4) ↪o Fin a := Q.orderEmbOfFin hQ'
  obtain ⟨i, j, hpar, hip, hjp, hui, huj⟩ := hgeometry f
  have hallowed :=
    p3PotentialPacket_allowed_of_protected_pair
      k a block protectedBlocks z hcover f i j hpar hip hjp hui huj
  change localIndex (p3HyperFromPotential (4*k+3) a z)
      (Q.orderEmbOfFin hQ').toEmbedding ∈
      toggleZero (switchingAllowed (4*k+3)) at hallowed
  simpa only [show 4*k+3+1 = 4*k+4 by omega] using hallowed

end Hypertournaments
