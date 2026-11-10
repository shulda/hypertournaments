import Hypertournaments.OnePointJoint
import Hypertournaments.OddToggleP1Homogeneous

/-!
# Canonical mixed packets and endpoint geometry for p1 non-amalgamation

An arbitrary ordinary amalgam of the two genuine one-point sides,
provided its new vertices remain distinct, restricts to the
canonical joint with 4k+8 vertices. Here the old vertices precede
the two new ones, which enables direct analysis of homogeneous mixed
packets by deleting two old vertices.

All statements concern genuine finite sets and intrinsic local
indices; no special order is assumed on the eventual amalgam.
-/

namespace Hypertournaments

def p1JointOld (k : ℕ) (v : Fin (4*k+6)) : Fin (4*k+6+2) :=
  ⟨v.val, by have hv := v.isLt; omega⟩

def p1JointLeftNew (k : ℕ) : Fin (4*k+6+2) :=
  ⟨4*k+6, by omega⟩

def p1JointRightNew (k : ℕ) : Fin (4*k+6+2) :=
  Fin.last (4*k+6+1)

theorem p1JointOld_lt_left (k : ℕ) (v : Fin (4*k+6)) :
    p1JointOld k v < p1JointLeftNew k := by
  change v.val < 4*k+6
  exact v.isLt

theorem p1JointLeft_lt_right (k : ℕ) :
    p1JointLeftNew k < p1JointRightNew k := by
  change 4*k+6 < 4*k+6+1
  omega

theorem p1JointOld_left_inclusion (k : ℕ) (v : Fin (4*k+6)) :
    leftJointInclusion (4*k+6) v.castSucc = p1JointOld k v := by
  apply Fin.ext
  rfl

theorem p1JointOld_right_inclusion (k : ℕ) (v : Fin (4*k+6)) :
    rightJointInclusion (4*k+6) v.castSucc = p1JointOld k v := by
  rw [rightJointInclusion_old]
  apply Fin.ext
  rfl

theorem p1JointLeftNew_inclusion (k : ℕ) :
    leftJointInclusion (4*k+6) (Fin.last (4*k+6)) =
      p1JointLeftNew k := by
  apply Fin.ext
  rfl

theorem p1JointRightNew_inclusion (k : ℕ) :
    rightJointInclusion (4*k+6) (Fin.last (4*k+6)) =
      p1JointRightNew k := by
  rw [rightJointInclusion_new]
  rfl

def p1JointMixedPacket (k : ℕ) (v w : Fin (4*k+6)) :
    Finset (Fin (4*k+6+2)) :=
  ((Finset.univ : Finset (Fin (4*k+6+2))).erase
    (p1JointOld k v)).erase (p1JointOld k w)

/-- Each mixed packet genuinely contains both new vertices. -/
theorem p1JointMixedPacket_new_mem
    (k : ℕ) (v w : Fin (4*k+6)) :
    p1JointLeftNew k ∈ p1JointMixedPacket k v w ∧
    p1JointRightNew k ∈ p1JointMixedPacket k v w := by
  have hLv : p1JointLeftNew k ≠ p1JointOld k v :=
    (ne_of_lt (p1JointOld_lt_left k v)).symm
  have hLw : p1JointLeftNew k ≠ p1JointOld k w :=
    (ne_of_lt (p1JointOld_lt_left k w)).symm
  have hRv : p1JointRightNew k ≠ p1JointOld k v :=
    (ne_of_lt (lt_trans (p1JointOld_lt_left k v)
      (p1JointLeft_lt_right k))).symm
  have hRw : p1JointRightNew k ≠ p1JointOld k w :=
    (ne_of_lt (lt_trans (p1JointOld_lt_left k w)
      (p1JointLeft_lt_right k))).symm
  constructor
  · exact Finset.mem_erase.mpr
      ⟨hLw, Finset.mem_erase.mpr ⟨hLv, Finset.mem_univ _⟩⟩
  · exact Finset.mem_erase.mpr
      ⟨hRw, Finset.mem_erase.mpr ⟨hRv, Finset.mem_univ _⟩⟩

/-- Deleting two distinct old vertices leaves exactly n+1
vertices, as required for a local packet in arity n=4k+5. -/
theorem p1JointMixedPacket_card (k : ℕ)
    (v w : Fin (4*k+6)) (hvw : v ≠ w) :
    (p1JointMixedPacket k v w).card = 4*k+6 := by
  have hne : p1JointOld k v ≠ p1JointOld k w := by
    intro he
    apply hvw
    apply Fin.ext
    have hval := congrArg Fin.val he
    change v.val = w.val at hval
    exact hval
  have hfirst :=
    Finset.card_erase_add_one
      (Finset.mem_univ (p1JointOld k v) :
        p1JointOld k v ∈ (Finset.univ : Finset (Fin (4*k+6+2))))
  have hsecond :=
    Finset.card_erase_add_one
      (Finset.mem_erase.mpr
        ⟨hne.symm, Finset.mem_univ _⟩ :
        p1JointOld k w ∈
          (Finset.univ : Finset (Fin (4*k+6+2))).erase
            (p1JointOld k v))
  dsimp [p1JointMixedPacket]
  simp only [Finset.card_univ, Fintype.card_fin] at hfirst
  omega

/-- The mixed packet does not depend on which missing old vertex
is erased first. -/
theorem p1JointMixedPacket_comm (k : ℕ)
    (v w : Fin (4*k+6)) :
    p1JointMixedPacket k v w = p1JointMixedPacket k w v := by
  ext x
  simp only [p1JointMixedPacket, Finset.mem_erase, Finset.mem_univ, and_true]
  tauto

/-- Homogeneous intrinsic packets have opposite raw orientations at
their final two facet positions, since normalization toggles parity. -/
theorem Hyper.p1Homogeneous_lastTwo_raw_ne
    (k : ℕ) {V : Type*} (A : Hyper (4*k+5) V)
    (f : Fin (4*k+6) ↪ V)
    (hzero : localIndex A f = 0) :
    A.orient (facet f ⟨4*k+4, by omega⟩) ≠
      A.orient (facet f ⟨4*k+5, by omega⟩) := by
  let i0 : Fin (4*k+6) := ⟨4*k+4, by omega⟩
  let i1 : Fin (4*k+6) := ⟨4*k+5, by omega⟩
  obtain ⟨b, hb⟩ := (localIndex_zero_iff_normalized_constant A f).mp hzero
  have heven : (4*k+4)%2 ≠ 1 := by omega
  have hodd : (4*k+5)%2 = 1 := by omega
  have h0 : normalizedFacet A f i0 = A.orient (facet f i0) := by
    change Bool.xor (A.orient (facet f i0))
      (decide ((4*k+4)%2=1)) = A.orient (facet f i0)
    simp [heven]
  have h1 : normalizedFacet A f i1 = !(A.orient (facet f i1)) := by
    change Bool.xor (A.orient (facet f i1))
      (decide ((4*k+5)%2=1)) = !(A.orient (facet f i1))
    simp [hodd]
  have hb0 := hb i0
  have hb1 := hb i1
  rw [h0] at hb0
  rw [h1] at hb1
  change A.orient (facet f i0) ≠ A.orient (facet f i1)
  intro heq
  rw [← heq] at hb1
  have hcontr : Bool.not (A.orient (facet f i0)) =
      A.orient (facet f i0) := hb1.trans hb0.symm
  cases hx : A.orient (facet f i0) <;> simp [hx] at hcontr

end Hypertournaments
