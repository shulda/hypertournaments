import Hypertournaments.OnePointNonmixedAdmissible
import Hypertournaments.OddToggleP1BaseAdmissible
import Hypertournaments.OddToggleP1SideEvenRows
import Hypertournaments.OddToggleP1SidePacketDichotomy

/-!
# Uniform p1 side age reduction to exact one-point packet obligations

The old-only packet of each side is identified with the intrinsically
admissible common base via the actual orientation-preserving
embedding. Every other packet is some omitted-old packet, and its
admissibility follows from matching canonical row parity OR genuine
homogeneous type zero. This is an exhaustive reduction, not an
assumption of side admissibility.
-/

namespace Hypertournaments

/-- The exact ordered enumeration of the unique old-only packet
is the canonical old-vertex embedding, in every arity n=4k+5. -/
theorem p1OldPacket_orderEmb_eq_inclusion
    (k : ℕ)
    (Q : Finset (Fin (4*k+6+1)))
    (hQ : Q.card = 4*k+6)
    (hOld : Q = (Finset.univ : Finset (Fin (4*k+6+1))).erase
      (Fin.last (4*k+6))) :
    (Fin.castSuccOrderEmb : Fin (4*k+6) ↪o Fin (4*k+6+1)) =
      Q.orderEmbOfFin hQ := by
  apply Finset.orderEmbOfFin_unique' hQ
  intro i
  rw [hOld, ← p1OldBaseImage_univ k]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

/-- The actual all-old packet in either side inherits its local
type from the already certified common base. -/
theorem p1Side_old_packet_allowed
    (k : ℕ) (left : Bool)
    (Q : Finset (Fin (4*k+6+1)))
    (hQ : Q.card = 4*k+6)
    (hOld : Q = (Finset.univ : Finset (Fin (4*k+6+1))).erase
      (Fin.last (4*k+6))) :
    localIndex (p1SideHyper k left) (Q.orderEmbOfFin hQ).toEmbedding ∈
      toggleZero (switchingAllowed (4*k+5)) := by
  have hemb := p1OldPacket_orderEmb_eq_inclusion k Q hQ hOld
  rw [← hemb]
  have he := localIndex_preserves
    (p1BaseHyper k) (p1SideHyper k left)
    (Fin.castSuccEmb : Fin (4*k+6) ↪ Fin (4*k+6+1))
    (p1SideHyper_preserves_base k left)
    (Function.Embedding.refl (Fin (4*k+6)))
  have hshift :
      (Function.Embedding.refl (Fin (4*k+6))).trans
        (Fin.castSuccEmb : Fin (4*k+6) ↪ Fin (4*k+6+1)) =
      (Fin.castSuccOrderEmb : Fin (4*k+6) ↪o Fin (4*k+6+1)).toEmbedding := by
    ext i
    rfl
  have hresult :
      localIndex (p1SideHyper k left)
        ((Fin.castSuccOrderEmb : Fin (4*k+6) ↪o Fin (4*k+6+1)).toEmbedding) =
      localIndex (p1BaseHyper k)
        (Function.Embedding.refl (Fin (4*k+6))) := by
    rw [← hshift]
    exact he.symm
  rw [hresult]
  exact p1BaseHyper_admissible k (Function.Embedding.refl _)

/-- The homogeneous local type zero belongs to the actual p1
allowed type family, uniformly in k. -/
theorem p1TypeZero_allowed (k : ℕ) :
    0 ∈ toggleZero (switchingAllowed (4*k+5)) := by
  change 0 ∉ switchingAllowed (4*k+5)
  intro hz
  have hp : 0%2 = (centralIndex (4*k+5))%2 := hz.2
  unfold centralIndex at hp
  omega

/-- To prove full actual admissibility for either one-point side,
it suffices to check, for every possible omitted old vertex, either
matching full canonical link-row parity or intrinsic index zero. -/
theorem p1Side_admissible_of_rows_or_zero
    (k : ℕ) (left : Bool)
    (hcases : ∀ v : Fin (4*k+6),
      ∀ hQ : (p1SidePacketOmitOld k v).card = 4*k+6,
      p1CanonicalRowPositiveCount k left v % 2 =
        (if p1BaseVertexBit k v then 1 else 0) ∨
      localIndex (p1SideHyper k left)
        ((p1SidePacketOmitOld k v).orderEmbOfFin hQ).toEmbedding = 0) :
    Admissible (toggleZero (switchingAllowed (4*k+5)))
      (p1SideHyper k left) := by
  apply (admissible_iff_canonical_all
    (toggleZero (switchingAllowed (4*k+5)))
    (p1SideHyper k left)).2
  intro Q hQ
  rcases p1SideSubset_old_or_omit k Q hQ with hOld | ⟨v, hv⟩
  · exact p1Side_old_packet_allowed k left Q hQ hOld
  · subst Q
    rcases hcases v hQ with hrow | hzero
    · apply p1SidePacket_allowed_of_rowParity k left v
        ((p1SidePacketOmitOld k v).orderEmbOfFin hQ)
        ?_ hrow
      simpa [tupleVertices] using
        (Finset.image_orderEmbOfFin_univ (p1SidePacketOmitOld k v) hQ)
    · rw [hzero]
      exact p1TypeZero_allowed k

end Hypertournaments
