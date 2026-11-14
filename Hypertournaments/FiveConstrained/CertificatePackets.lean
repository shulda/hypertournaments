import Hypertournaments.FiveConstrained.PacketSemantics
import Hypertournaments.FiveConstrained.CertificateStructures

/-!
# Local packets of the actual certificate sides and joints

These formulas identify the executable requirements with actual induced
intrinsic structures. They retain the literal original vertex embeddings.
-/

namespace Hypertournaments.FiveConstrained

/-- Increasing four-tuple on explicitly chosen vertices. -/
def fourEmbedding {n : ℕ} (a b c d : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d) : Fin 4 ↪ Fin n where
  toFun := ![a, b, c, d]
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all <;> omega

@[simp] theorem fourEmbedding_apply {n : ℕ} (a b c d : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d) (i : Fin 4) :
    fourEmbedding a b c d hab hbc hcd i = ![a, b, c, d] i := rfl

theorem fourEmbedding_strictMono {n : ℕ} (a b c d : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    StrictMono (fourEmbedding a b c d hab hbc hcd : Fin 4 → Fin n) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all <;> omega

/-- Increasing five-tuple on explicitly chosen vertices. -/
def fiveEmbedding {n : ℕ} (a b c d e : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e) : Fin 5 ↪ Fin n where
  toFun := ![a, b, c, d, e]
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all <;> omega

@[simp] theorem fiveEmbedding_apply {n : ℕ} (a b c d e : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e) (i : Fin 5) :
    fiveEmbedding a b c d e hab hbc hcd hde i = ![a, b, c, d, e] i := rfl

theorem fiveEmbedding_strictMono {n : ℕ} (a b c d e : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e) :
    StrictMono (fiveEmbedding a b c d e hab hbc hcd hde : Fin 5 → Fin n) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all <;> omega

namespace CertificateDiagram

/-- Actual four-type of a side, on any increasing four-tuple. -/
theorem side_localIndex (d : CertificateDiagram) (b : Bool)
    (e : Fin 4 ↪ Fin (d.baseSize + 1))
    (he : StrictMono (e : Fin 4 → Fin (d.baseSize + 1))) :
    localIndex (d.sideHyper b) e =
      certificateSideType4 d b ((e 0).val, (e 1).val, (e 2).val, (e 3).val) := by
  have hbit (i : Fin 4) :
      (d.sideHyper b).orient ((triple4 i).trans e) =
        d.sideBit b (e (triple4 i 0)).val (e (triple4 i 1)).val (e (triple4 i 2)).val :=
    sideHyper_orient_increasing d b _ (he.comp (triple4_strictMono i))
  rw [localIndex_eq_certificateType4_at]
  simp_rw [hbit]
  rfl

/-- Actual ten-bit packet of a side, on any increasing five-tuple. -/
theorem side_packet5 (d : CertificateDiagram) (b : Bool)
    (e : Fin 5 ↪ Fin (d.baseSize + 1))
    (he : StrictMono (e : Fin 5 → Fin (d.baseSize + 1))) :
    packet5OfHyper ((d.sideHyper b).pullback e) =
      certificateSidePacket5 d b ((e 0).val, (e 1).val, (e 2).val, (e 3).val, (e 4).val) := by
  have hbit (i : Fin 10) :
      ((d.sideHyper b).pullback e).orient (triple5 i) =
        d.sideBit b (e (triple5 i 0)).val (e (triple5 i 1)).val (e (triple5 i 2)).val :=
    sideHyper_orient_increasing d b _ (he.comp (triple5_strictMono i))
  unfold packet5OfHyper
  simp_rw [hbit]
  rfl

/-- Four-type of a canonical joint, on an arbitrary increasing four-tuple. -/
theorem joint_localIndex (d : CertificateDiagram) (x : ℕ)
    (e : Fin 4 ↪ Fin (d.baseSize + 2))
    (he : StrictMono (e : Fin 4 → Fin (d.baseSize + 2))) :
    localIndex (d.jointHyper x) e =
      certificateType4
        (d.jointBit x (e 0).val (e 1).val (e 2).val)
        (d.jointBit x (e 0).val (e 1).val (e 3).val)
        (d.jointBit x (e 0).val (e 2).val (e 3).val)
        (d.jointBit x (e 1).val (e 2).val (e 3).val) := by
  have hbit (i : Fin 4) :
      (d.jointHyper x).orient ((triple4 i).trans e) =
        d.jointBit x (e (triple4 i 0)).val (e (triple4 i 1)).val (e (triple4 i 2)).val :=
    jointHyper_orient_increasing d x _ (he.comp (triple4_strictMono i))
  rw [localIndex_eq_certificateType4_at]
  simp_rw [hbit]
  rfl

/-- Five-packet of a canonical joint, on an arbitrary increasing five-tuple. -/
theorem joint_packet5 (d : CertificateDiagram) (x : ℕ)
    (e : Fin 5 ↪ Fin (d.baseSize + 2))
    (he : StrictMono (e : Fin 5 → Fin (d.baseSize + 2))) :
    packet5OfHyper ((d.jointHyper x).pullback e) =
      certificatePacket5
        (d.jointBit x (e 0).val (e 1).val (e 2).val)
        (d.jointBit x (e 0).val (e 1).val (e 3).val)
        (d.jointBit x (e 0).val (e 1).val (e 4).val)
        (d.jointBit x (e 0).val (e 2).val (e 3).val)
        (d.jointBit x (e 0).val (e 2).val (e 4).val)
        (d.jointBit x (e 0).val (e 3).val (e 4).val)
        (d.jointBit x (e 1).val (e 2).val (e 3).val)
        (d.jointBit x (e 1).val (e 2).val (e 4).val)
        (d.jointBit x (e 1).val (e 3).val (e 4).val)
        (d.jointBit x (e 2).val (e 3).val (e 4).val) := by
  have hbit (i : Fin 10) :
      ((d.jointHyper x).pullback e).orient (triple5 i) =
        d.jointBit x (e (triple5 i 0)).val (e (triple5 i 1)).val (e (triple5 i 2)).val :=
    jointHyper_orient_increasing d x _ (he.comp (triple5_strictMono i))
  unfold packet5OfHyper
  simp_rw [hbit]
  rfl

/-- The four-tuple formed by two old points and the two new points. -/
def mixed_fourTuple (d : CertificateDiagram) (a b : Fin d.baseSize) (hab : a < b) :
    Fin 4 ↪ Fin (d.baseSize + 2) :=
  fourEmbedding a.castSucc.castSucc b.castSucc.castSucc
    (Fin.last d.baseSize).castSucc (Fin.last (d.baseSize + 1)) hab b.isLt (by simp)

theorem mixed_fourTuple_strictMono (d : CertificateDiagram)
    (a b : Fin d.baseSize) (hab : a < b) :
    StrictMono (d.mixed_fourTuple a b hab : Fin 4 → Fin (d.baseSize + 2)) :=
  fourEmbedding_strictMono _ _ _ _ _ _ _

/-- The five-tuple formed by three old points and the two new points. -/
def mixed_fiveTuple (d : CertificateDiagram) (a b c : Fin d.baseSize)
    (hab : a < b) (hbc : b < c) : Fin 5 ↪ Fin (d.baseSize + 2) :=
  fiveEmbedding a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc
    (Fin.last d.baseSize).castSucc (Fin.last (d.baseSize + 1)) hab hbc c.isLt (by simp)

theorem mixed_fiveTuple_strictMono (d : CertificateDiagram)
    (a b c : Fin d.baseSize) (hab : a < b) (hbc : b < c) :
    StrictMono (d.mixed_fiveTuple a b c hab hbc : Fin 5 → Fin (d.baseSize + 2)) :=
  fiveEmbedding_strictMono _ _ _ _ _ _ _ _ _

theorem mixed_localIndex (d : CertificateDiagram) (x : ℕ)
    (a b : Fin d.baseSize) (hab : a < b) :
    localIndex (d.jointHyper x) (d.mixed_fourTuple a b hab) =
      certificateMixedType4 d x a.val b.val := by
  rw [joint_localIndex d x _ (mixed_fourTuple_strictMono d a b hab)]
  simp [mixed_fourTuple, jointBit, sideBit, certificateMixedType4,
    b.isLt]

theorem mixed_packet5 (d : CertificateDiagram) (x : ℕ)
    (a b c : Fin d.baseSize) (hab : a < b) (hbc : b < c) :
    packet5OfHyper ((d.jointHyper x).pullback (d.mixed_fiveTuple a b c hab hbc)) =
      certificateMixedPacket5 d x a.val b.val c.val := by
  rw [joint_packet5 d x _ (mixed_fiveTuple_strictMono d a b c hab hbc)]
  simp [mixed_fiveTuple, jointBit, sideBit, certificateMixedPacket5,
    b.isLt, c.isLt, show c.val < d.baseSize + 1 by omega]

end CertificateDiagram
end Hypertournaments.FiveConstrained
