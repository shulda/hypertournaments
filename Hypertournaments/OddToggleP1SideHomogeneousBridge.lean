import Hypertournaments.OddToggleP1SidePacketIndex
import Hypertournaments.OddToggleP1OmissionAllLinks
import Hypertournaments.OddToggleP1RawAlternating

/-!
# Genuine p1 side homogeneous packets from exact alternating link rows

The actual finite sign-table side is a bona fide hypertournament.
If, for a deleted old vertex v, its canonical link row alternates
with the increasing packet deletion index, and the omitted old base
bit gives the same alternation at the final new-vertex facet, then
the complete true local packet has normalized type zero.

This bridge is independent of the two particular protected vertices
a0 and a4. It is uniform in k and has no admissibility hypothesis.
-/

namespace Hypertournaments

/-- A source sign-table link row and the final base facet determine
every actual raw packet orientation, including the deleted new
vertex facet, when the row is prescribed by one alternating phase. -/
theorem p1SidePacket_raw_alternating_of_link
    (k : ℕ) (v : Fin (4*k+6))
    (b : Bool)
    (hlink : ∀ w : Fin (4*k+6), w ≠ v →
      p1CanonicalLink k false v w =
        (b ^^ decide (((if w.val < v.val then w.val else w.val-1)%2)=1)))
    (hlast : p1BaseVertexBit k v =
      (b ^^ decide (((4*k+5)%2)=1)))
    (hQ : (p1SidePacketOmitOld k v).card = 4*k+6)
    (i : Fin (4*k+6)) :
    (p1SideHyper k false).orient
       (facet ((p1SidePacketOmitOld k v).orderEmbOfFin hQ).toEmbedding i) =
       (b ^^ decide (i.val%2=1)) := by
  let Q : Finset (Fin (4*k+6+1)) := p1SidePacketOmitOld k v
  let g : Fin (4*k+6) ↪o Fin (4*k+6+1) := Q.orderEmbOfFin hQ
  have hverts : tupleVertices g.toEmbedding = Q := by
    simpa [tupleVertices, g] using
      (Finset.image_orderEmbOfFin_univ Q hQ)
  have hraw :
      (p1SideHyper k false).orient (facet g.toEmbedding i) =
        p1SideSignTable k false (Q.erase (g i)) := by
    calc
      (p1SideHyper k false).orient (facet g.toEmbedding i) =
          p1SideSignTable k false
            (tupleVertices (facet g.toEmbedding i)) :=
        fromOrderedSigns_facet_increasing (p1SideSignTable k false) g i
      _ = p1SideSignTable k false (Q.erase (g i)) := by
        rw [tupleVertices_facet_eq_erase, hverts]
        rfl
  by_cases hi : i.val < 4*k+5
  · obtain ⟨w, hwne, hwi, hpos⟩ :=
      p1SidePacket_old_position k v hQ i hi
    rw [hraw, hwi]
    rw [p1SidePacket_sign_erase_old_ne k false v w hwne]
    rw [hlink w hwne]
    rw [hpos]
  · have heq : i = Fin.last (4*k+5) := by
      apply Fin.ext
      have hib := i.isLt
      omega
    subst i
    rw [hraw, p1SidePacket_last_is_new k v hQ]
    rw [p1SidePacket_sign_erase_new k false v, hlast]
    rfl

/-- Under the actual-row alternation hypothesis, the genuine
right-side ordered packet omitting v has intrinsic localIndex 0. -/
theorem p1SidePacket_localIndex_zero_of_link
    (k : ℕ) (v : Fin (4*k+6))
    (b : Bool)
    (hlink : ∀ w : Fin (4*k+6), w ≠ v →
      p1CanonicalLink k false v w =
        (b ^^ decide (((if w.val < v.val then w.val else w.val-1)%2)=1)))
    (hlast : p1BaseVertexBit k v =
      (b ^^ decide (((4*k+5)%2)=1)))
    (hQ : (p1SidePacketOmitOld k v).card = 4*k+6) :
    localIndex (p1SideHyper k false)
      ((p1SidePacketOmitOld k v).orderEmbOfFin hQ).toEmbedding = 0 := by
  apply (localIndex_zero_iff_normalized_constant
    (p1SideHyper k false)
    ((p1SidePacketOmitOld k v).orderEmbOfFin hQ).toEmbedding).2
  refine ⟨b, ?_⟩
  intro i
  have hraw := p1SidePacket_raw_alternating_of_link
    k v b hlink hlast hQ i
  change Bool.xor
    ((p1SideHyper k false).orient
      (facet ((p1SidePacketOmitOld k v).orderEmbOfFin hQ).toEmbedding i))
    (decide (i.val%2=1)) = b
  rw [hraw]
  cases b <;> cases h : decide (i.val%2=1) <;>
    simp [h]

end Hypertournaments
