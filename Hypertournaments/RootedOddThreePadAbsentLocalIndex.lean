import Hypertournaments.RootedOddThreePadAbsentPacket
import Hypertournaments.RootedOddThreePadIndexShift
import Hypertournaments.RootZeroPrefixOldTuple
import Hypertournaments.RootedOddThreePadOldTail

/-!
# Actual local-index shift for root-absent three-pad odd suspension packets

This combines the verified raw facet signs, full normalized packet
identity, increasing old-tail extraction, root-zero prefix geometry,
and intrinsic Boolean +1 minority-count shift. The conclusion refers
to an actual old (n+1)-tuple and actual old local index, not merely
an abstract Boolean packet.
-/

namespace Hypertournaments

/-- Every root-absent, increasing three-pad packet of the canonical
rooted odd suspension has local index equal to an actual old local
index plus one. -/
theorem Hyper.rootedOddSuspension_localIndex_threePads_rootZero_absent
    (k m a : ℕ) (A : Hyper (2*k+1) (Fin a))
    (root : Fin a) (hroot0 : root.val = 0)
    (f : Fin (2*k+4) ↪o Fin (m+a))
    (hthree :
      (evenPadProjection m a (tupleVertices f.toEmbedding)).card = 3)
    (habsent :
      root ∉ evenOldProjection m a (tupleVertices f.toEmbedding)) :
    ∃ g : Fin (2*k+2) ↪o Fin a,
      localIndex (A.rootedOddSuspension m a root) f.toEmbedding =
        localIndex A g.toEmbedding + 1 := by
  obtain ⟨t, htCoords, htVertices⟩ :=
    evenOldTail_of_increasing_threePads f hthree
  have hnot : root ∉ tupleVertices t.toEmbedding := by
    rw [← htVertices]
    exact habsent
  obtain ⟨g, hgRoot, hgTail, hgVertices⟩ :=
    exists_increasing_tuple_prefix_zero_root root hroot0 t hnot
  have htail : ∀ j : Fin (2*k+1),
      f j.succ.succ.succ = evenOldShift m a (g j.succ) := by
    intro j
    calc
      f j.succ.succ.succ = evenOldShift m a (t j) := (htCoords j).symm
      _ = evenOldShift m a (g j.succ) := by rw [hgTail j]
  have hverts :
      tupleVertices g.toEmbedding =
        insert root (evenOldProjection m a (tupleVertices f.toEmbedding)) := by
    rw [hgVertices, htVertices]
  refine ⟨g, ?_⟩
  exact localIndex_threePad_prefix_shift_of_packet
    A (A.rootedOddSuspension m a root) g.toEmbedding f.toEmbedding
    (A.rootedOddSuspension_threePads_rootAbsent_packetEq
      root f hthree habsent g hgRoot htail hverts)

end Hypertournaments
