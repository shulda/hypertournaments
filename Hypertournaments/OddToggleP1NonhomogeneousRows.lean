import Hypertournaments.OddToggleP1RawCountParity
import Hypertournaments.OddToggleP1SidesAdmissible
import Hypertournaments.OddToggleP1RowMatchesBase

/-!
# Actual even-raw local packets cannot be homogeneous in the p1 age

On n=4k+5, the intrinsic type-zero indicator equals the parity
of the raw positive facet count on every admissible packet. Thus
an even raw count entails nonhomogeneity. Apply to every left
old-omission packet and every right old-omission packet except the
two protected vertices a0 and a4, using their certified row parity.
This identifies exactly which one-point facets may be the fixed
homogeneous edges in the mixed-joint nonamalgamation argument.
-/

namespace Hypertournaments

/-- Every even-raw packet in an actual admissible p1 hypertournament
has nonzero intrinsic local index. -/
theorem Hyper.p1Toggle_nonhomogeneous_of_even_raw
    (k : ℕ) {V : Type*}
    (A : Hyper (4*k+5) V)
    (hA : Admissible (toggleZero (switchingAllowed (4*k+5))) A)
    (f : Fin (4*k+6) ↪ V)
    (heven : boolPacketPositiveCount
      (fun i : Fin (4*k+6) => A.orient (facet f i)) % 2 = 0) :
    localIndex A f ≠ 0 := by
  have hr :
      ((boolPacketPositiveCount
        (fun i : Fin (4*k+6) => A.orient (facet f i)) : ℕ) : ZMod 2) = 0 := by
    rw [p1NatCast_eq_oddBit]
    simp [heven, p1BitToZMod]
  have h0 := A.p1Toggle_typeZero_iff_rawFacetParityOne k f (hA f)
  have hzero : p1BitToZMod (decide (localIndex A f = 0)) = 0 :=
    h0.trans hr
  intro hz
  have hone : (1 : ZMod 2) = 0 := by
    simpa [hz, p1BitToZMod] using hzero
  exact (by decide : (1 : ZMod 2) ≠ 0) hone

/-- The entire explicit p1 left side has no homogeneous
old-omission packet, for every k and every increasing enumeration. -/
theorem p1LeftSide_omission_nonhomogeneous
    (k : ℕ) (v : Fin (4*k+6))
    (g : Fin (4*k+6) ↪o Fin (4*k+6+1))
    (hg : tupleVertices g.toEmbedding = p1SidePacketOmitOld k v) :
    localIndex (p1SideHyper k true) g.toEmbedding ≠ 0 := by
  have heven := p1SidePacket_rawEven_of_rowParity k true v g hg
    (p1CanonicalLeft_row_matches_base k v)
  exact (p1SideHyper k true).p1Toggle_nonhomogeneous_of_even_raw
    k (p1LeftSide_admissible k) g.toEmbedding heven

/-- Every unprotected actual right p1 old-omission packet
has nonzero intrinsic local index. -/
theorem p1RightSide_omission_unprotected_nonhomogeneous
    (k : ℕ) (v : Fin (4*k+6))
    (hzero : v ≠ p1CoreAt k (0 : Fin 6))
    (hfour : v ≠ p1CoreAt k (4 : Fin 6))
    (g : Fin (4*k+6) ↪o Fin (4*k+6+1))
    (hg : tupleVertices g.toEmbedding = p1SidePacketOmitOld k v) :
    localIndex (p1SideHyper k false) g.toEmbedding ≠ 0 := by
  have heven := p1SidePacket_rawEven_of_rowParity k false v g hg
    (p1CanonicalRight_row_matches_base_unprotected k v hzero hfour)
  exact (p1SideHyper k false).p1Toggle_nonhomogeneous_of_even_raw
    k (p1RightSide_admissible k) g.toEmbedding heven

end Hypertournaments
