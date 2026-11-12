import Hypertournaments.OddToggleP3FreshOldEnum

/-!
# Exact old-vertex set of a canonical one-fresh packet

The preceding old-enumeration theorem produces U and its increasing
enumeration. Here we identify U with the PRECISE preimage of the
packet's old vertices under Fin.castSuccOrderEmb. This rules out
hidden extra or missing old vertices in the transfer of the p3
block-occupancy and singleton-facet arguments.

The fresh vertex is only a coordinate convention, not an additional
relation or part of the hypertournament language.
-/

namespace Hypertournaments

/-- The canonical old subset of a fresh-containing packet is
exactly the set of old vertices whose inclusion appears in that
packet, with the same increasing prefix enumeration. -/
theorem p3CanonicalFresh_old_enumeration_membership
    (a n : ℕ) (f : Fin (n+1) ↪o Fin (a+1))
    (hFresh : Fin.last a ∈ tupleVertices f.toEmbedding) :
    ∃ (U : Finset (Fin a)) (hU : U.card = n),
      (∀ i : Fin n,
        (U.orderEmbOfFin hU i).castSucc = f i.castSucc) ∧
      (∀ v : Fin a,
        v ∈ U ↔ v.castSucc ∈ tupleVertices f.toEmbedding) := by
  classical
  obtain ⟨U, hU, hEnum⟩ :=
    p3CanonicalFresh_old_enumeration a n f hFresh
  refine ⟨U, hU, hEnum, ?_⟩
  intro v
  constructor
  · intro hv
    have hvImage :
        v ∈ (Finset.univ : Finset (Fin n)).image
          (U.orderEmbOfFin hU) := by
      simpa only [Finset.image_orderEmbOfFin_univ U hU] using hv
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hvImage
    apply Finset.mem_image.mpr
    refine ⟨i.castSucc, Finset.mem_univ _, ?_⟩
    change f i.castSucc = v.castSucc
    calc
      f i.castSucc = (U.orderEmbOfFin hU i).castSucc :=
        (hEnum i).symm
      _ = v.castSucc := congrArg Fin.castSucc hi
  · intro hv
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hv
    change f j = v.castSucc at hj
    rcases j.eq_castSucc_or_eq_last with ⟨i, rfl⟩ | rfl
    · have hOld :
          U.orderEmbOfFin hU i = v :=
        (Fin.castSuccOrderEmb : Fin a ↪o Fin (a+1)).injective
          ((hEnum i).trans hj)
      rw [← hOld]
      have hi :
          (U.orderEmbOfFin hU i) ∈
            (Finset.univ : Finset (Fin n)).image
              (U.orderEmbOfFin hU) :=
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      simpa only [Finset.image_orderEmbOfFin_univ U hU] using hi
    · have hLast :=
        p3CanonicalFresh_is_last_packet_position a n f hFresh
      rw [hLast] at hj
      exact False.elim ((Fin.castSucc_ne_last v) hj.symm)

end Hypertournaments
