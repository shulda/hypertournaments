import Hypertournaments.OddToggleP1MissingSets
import Hypertournaments.OddToggleP1CoreRows
import Hypertournaments.CanonicalPacket

/-!
# Genuine left-right orientation disagreement from the core pair 24

The uniform p1 one-point sides are built using canonical tables.
On an n-subset containing the new endpoint and missing precisely
the base core vertices a2,a4, their raw increasing orientations
are different: the finite six-core matrices give left=false,
right=true.

These statements exclude identification of the two new endpoints
in any ordinary amalgam once we construct an actual n-tuple
with that precise underlying set.
-/

namespace Hypertournaments

/-- The canonical pair a2,a4 is increasing within the old base. -/
theorem p1CoreAt_two_lt_four (k : ℕ) :
    p1CoreAt k (2 : Fin 6) < p1CoreAt k (4 : Fin 6) := by
  change 4*k+2 < 4*k+4
  omega

/-- The concrete canonical raw link tables disagree at 24. -/
theorem p1CanonicalLink_core_24_disagree (k : ℕ) :
    p1CanonicalLink k true
      (p1CoreAt k (2 : Fin 6)) (p1CoreAt k (4 : Fin 6)) ≠
    p1CanonicalLink k false
      (p1CoreAt k (2 : Fin 6)) (p1CoreAt k (4 : Fin 6)) := by
  rw [p1CanonicalLink_core_left, p1CanonicalLink_core_right]
  have hbits :
      p1CoreLeftSymBit (2 : Fin 6) (4 : Fin 6) = false ∧
      p1CoreRightSymBit (2 : Fin 6) (4 : Fin 6) = true := by
    decide
  simp [hbits.1, hbits.2]

/-- Any side n-set containing the new endpoint and omitting just
a2,a4 reads two different raw signs on the actual sides. -/
theorem p1SideSignTable_core_24_disagree
    (k : ℕ) (Q : Finset (Fin (4*k+6+1)))
    (hend : Fin.last (4*k+6) ∈ Q)
    (hmiss : p1MissingBase k Q =
      ({p1CoreAt k (2 : Fin 6), p1CoreAt k (4 : Fin 6)} :
        Finset (Fin (4*k+6)))) :
    p1SideSignTable k true Q ≠ p1SideSignTable k false Q := by
  unfold p1SideSignTable
  simp only [if_pos hend, hmiss]
  have hlt := p1CoreAt_two_lt_four k
  rw [p1PairMissingBit_pair k true _ _ hlt,
      p1PairMissingBit_pair k false _ _ hlt]
  exact p1CanonicalLink_core_24_disagree k

/-- Under the same hypotheses, the two *intrinsic* hypertournament
orientations disagree on the canonical increasing enumeration of Q. -/
theorem p1SideHyper_core_24_orient_disagree
    (k : ℕ) (Q : Finset (Fin (4*k+6+1)))
    (hQ : Q.card = 4*k+5)
    (hend : Fin.last (4*k+6) ∈ Q)
    (hmiss : p1MissingBase k Q =
      ({p1CoreAt k (2 : Fin 6), p1CoreAt k (4 : Fin 6)} :
        Finset (Fin (4*k+6)))) :
    (p1SideHyper k true).orient (Q.orderEmbOfFin hQ).toEmbedding ≠
      (p1SideHyper k false).orient (Q.orderEmbOfFin hQ).toEmbedding := by
  let t : Fin (4*k+5) ↪o Fin (4*k+6+1) := Q.orderEmbOfFin hQ
  have hvertices : tupleVertices t.toEmbedding = Q := by
    change Finset.univ.image (Q.orderEmbOfFin hQ) = Q
    exact Finset.image_orderEmbOfFin_univ Q hQ
  have htable (left : Bool) :
      (p1SideHyper k left).orient t.toEmbedding =
        p1SideSignTable k left Q := by
    change (Hyper.fromOrderedSigns (p1SideSignTable k left)).orient
      t.toEmbedding = _
    rw [fromOrderedSigns_orient_strictMono
      (p1SideSignTable k left) t.toEmbedding t.strictMono, hvertices]
  have hbad := p1SideSignTable_core_24_disagree k Q hend hmiss
  simpa only [htable true, htable false] using hbad

end Hypertournaments
