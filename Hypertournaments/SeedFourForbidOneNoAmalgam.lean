import Hypertournaments.OnePointJoint
import Hypertournaments.SeedFourForbidOneData
import Hypertournaments.SeedFourForbidOnePacket

/-!
# Complete ordinary AP obstruction for the class forbidding T_{4,1}

The common six-vertex base and its two seven-vertex one-point
extensions are the exact finite sign tables in the mathematical
technical note. Every mixed five-tuple (left,i,j,k,right), with
0 <= i < j < k <= 5, contributes one T, C-minus, or C-plus constraint. These
twenty constraints contradict the kernel-checked 15-Boolean theorem.

This file connects the finite certificate with actual intrinsic
hypertournament orientations and ordinary (not merely strong)
amalgamation. No theorem is postulated as an axiom.
-/

namespace Hypertournaments

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

private def pair12 : Fin 4 ↪ Fin 8 := ⟨![6,1,2,7], by decide⟩
private def pair13 : Fin 4 ↪ Fin 8 := ⟨![6,1,3,7], by decide⟩
private def pair14 : Fin 4 ↪ Fin 8 := ⟨![6,1,4,7], by decide⟩
private def pair15 : Fin 4 ↪ Fin 8 := ⟨![6,1,5,7], by decide⟩
private def pair23 : Fin 4 ↪ Fin 8 := ⟨![6,2,3,7], by decide⟩
private def pair24 : Fin 4 ↪ Fin 8 := ⟨![6,2,4,7], by decide⟩
private def pair25 : Fin 4 ↪ Fin 8 := ⟨![6,2,5,7], by decide⟩
private def pair34 : Fin 4 ↪ Fin 8 := ⟨![6,3,4,7], by decide⟩
private def pair35 : Fin 4 ↪ Fin 8 := ⟨![6,3,5,7], by decide⟩
private def pair45 : Fin 4 ↪ Fin 8 := ⟨![6,4,5,7], by decide⟩
private def pair01 : Fin 4 ↪ Fin 8 := ⟨![6,0,1,7], by decide⟩
private def pair02 : Fin 4 ↪ Fin 8 := ⟨![6,0,2,7], by decide⟩
private def pair03 : Fin 4 ↪ Fin 8 := ⟨![6,0,3,7], by decide⟩
private def pair04 : Fin 4 ↪ Fin 8 := ⟨![6,0,4,7], by decide⟩
private def pair05 : Fin 4 ↪ Fin 8 := ⟨![6,0,5,7], by decide⟩

private def frame012 : Fin 5 ↪ Fin 8 := ⟨![6,0,1,2,7], by decide⟩
private def left012 : Fin 4 ↪ Fin 7 := ⟨![6,0,1,2], by decide⟩
private def right012 : Fin 4 ↪ Fin 7 := ⟨![0,1,2,6], by decide⟩
private def frame013 : Fin 5 ↪ Fin 8 := ⟨![6,0,1,3,7], by decide⟩
private def left013 : Fin 4 ↪ Fin 7 := ⟨![6,0,1,3], by decide⟩
private def right013 : Fin 4 ↪ Fin 7 := ⟨![0,1,3,6], by decide⟩
private def frame014 : Fin 5 ↪ Fin 8 := ⟨![6,0,1,4,7], by decide⟩
private def left014 : Fin 4 ↪ Fin 7 := ⟨![6,0,1,4], by decide⟩
private def right014 : Fin 4 ↪ Fin 7 := ⟨![0,1,4,6], by decide⟩
private def frame015 : Fin 5 ↪ Fin 8 := ⟨![6,0,1,5,7], by decide⟩
private def left015 : Fin 4 ↪ Fin 7 := ⟨![6,0,1,5], by decide⟩
private def right015 : Fin 4 ↪ Fin 7 := ⟨![0,1,5,6], by decide⟩
private def frame023 : Fin 5 ↪ Fin 8 := ⟨![6,0,2,3,7], by decide⟩
private def left023 : Fin 4 ↪ Fin 7 := ⟨![6,0,2,3], by decide⟩
private def right023 : Fin 4 ↪ Fin 7 := ⟨![0,2,3,6], by decide⟩
private def frame024 : Fin 5 ↪ Fin 8 := ⟨![6,0,2,4,7], by decide⟩
private def left024 : Fin 4 ↪ Fin 7 := ⟨![6,0,2,4], by decide⟩
private def right024 : Fin 4 ↪ Fin 7 := ⟨![0,2,4,6], by decide⟩
private def frame025 : Fin 5 ↪ Fin 8 := ⟨![6,0,2,5,7], by decide⟩
private def left025 : Fin 4 ↪ Fin 7 := ⟨![6,0,2,5], by decide⟩
private def right025 : Fin 4 ↪ Fin 7 := ⟨![0,2,5,6], by decide⟩
private def frame034 : Fin 5 ↪ Fin 8 := ⟨![6,0,3,4,7], by decide⟩
private def left034 : Fin 4 ↪ Fin 7 := ⟨![6,0,3,4], by decide⟩
private def right034 : Fin 4 ↪ Fin 7 := ⟨![0,3,4,6], by decide⟩
private def frame035 : Fin 5 ↪ Fin 8 := ⟨![6,0,3,5,7], by decide⟩
private def left035 : Fin 4 ↪ Fin 7 := ⟨![6,0,3,5], by decide⟩
private def right035 : Fin 4 ↪ Fin 7 := ⟨![0,3,5,6], by decide⟩
private def frame045 : Fin 5 ↪ Fin 8 := ⟨![6,0,4,5,7], by decide⟩
private def left045 : Fin 4 ↪ Fin 7 := ⟨![6,0,4,5], by decide⟩
private def right045 : Fin 4 ↪ Fin 7 := ⟨![0,4,5,6], by decide⟩
private def frame123 : Fin 5 ↪ Fin 8 := ⟨![6,1,2,3,7], by decide⟩
private def left123 : Fin 4 ↪ Fin 7 := ⟨![6,1,2,3], by decide⟩
private def right123 : Fin 4 ↪ Fin 7 := ⟨![1,2,3,6], by decide⟩
private def frame124 : Fin 5 ↪ Fin 8 := ⟨![6,1,2,4,7], by decide⟩
private def left124 : Fin 4 ↪ Fin 7 := ⟨![6,1,2,4], by decide⟩
private def right124 : Fin 4 ↪ Fin 7 := ⟨![1,2,4,6], by decide⟩
private def frame125 : Fin 5 ↪ Fin 8 := ⟨![6,1,2,5,7], by decide⟩
private def left125 : Fin 4 ↪ Fin 7 := ⟨![6,1,2,5], by decide⟩
private def right125 : Fin 4 ↪ Fin 7 := ⟨![1,2,5,6], by decide⟩
private def frame134 : Fin 5 ↪ Fin 8 := ⟨![6,1,3,4,7], by decide⟩
private def left134 : Fin 4 ↪ Fin 7 := ⟨![6,1,3,4], by decide⟩
private def right134 : Fin 4 ↪ Fin 7 := ⟨![1,3,4,6], by decide⟩
private def frame135 : Fin 5 ↪ Fin 8 := ⟨![6,1,3,5,7], by decide⟩
private def left135 : Fin 4 ↪ Fin 7 := ⟨![6,1,3,5], by decide⟩
private def right135 : Fin 4 ↪ Fin 7 := ⟨![1,3,5,6], by decide⟩
private def frame145 : Fin 5 ↪ Fin 8 := ⟨![6,1,4,5,7], by decide⟩
private def left145 : Fin 4 ↪ Fin 7 := ⟨![6,1,4,5], by decide⟩
private def right145 : Fin 4 ↪ Fin 7 := ⟨![1,4,5,6], by decide⟩
private def frame234 : Fin 5 ↪ Fin 8 := ⟨![6,2,3,4,7], by decide⟩
private def left234 : Fin 4 ↪ Fin 7 := ⟨![6,2,3,4], by decide⟩
private def right234 : Fin 4 ↪ Fin 7 := ⟨![2,3,4,6], by decide⟩
private def frame235 : Fin 5 ↪ Fin 8 := ⟨![6,2,3,5,7], by decide⟩
private def left235 : Fin 4 ↪ Fin 7 := ⟨![6,2,3,5], by decide⟩
private def right235 : Fin 4 ↪ Fin 7 := ⟨![2,3,5,6], by decide⟩
private def frame245 : Fin 5 ↪ Fin 8 := ⟨![6,2,4,5,7], by decide⟩
private def left245 : Fin 4 ↪ Fin 7 := ⟨![6,2,4,5], by decide⟩
private def right245 : Fin 4 ↪ Fin 7 := ⟨![2,4,5,6], by decide⟩
private def frame345 : Fin 5 ↪ Fin 8 := ⟨![6,3,4,5,7], by decide⟩
private def left345 : Fin 4 ↪ Fin 7 := ⟨![6,3,4,5], by decide⟩
private def right345 : Fin 4 ↪ Fin 7 := ⟨![3,4,5,6], by decide⟩

/-- A rotation taking the last vertex of a four-tuple to its front
is odd, giving the correct sign of the left source links. -/
private def frontShift4Forbid : Equiv.Perm (Fin 4) :=
  (Equiv.swap (2 : Fin 4) 3) *
    (Equiv.swap (1 : Fin 4) 2) *
    (Equiv.swap (0 : Fin 4) 1)

private theorem frontShift4Forbid_odd :
    frontShift4Forbid.sign ≠ (1 : ℤˣ) := by
  have h23 : (Equiv.swap (2 : Fin 4) 3).sign = (-1 : ℤˣ) :=
    Equiv.Perm.sign_swap (by decide)
  have h12 : (Equiv.swap (1 : Fin 4) 2).sign = (-1 : ℤˣ) :=
    Equiv.Perm.sign_swap (by decide)
  have h01 : (Equiv.swap (0 : Fin 4) 1).sign = (-1 : ℤˣ) :=
    Equiv.Perm.sign_swap (by decide)
  have h : frontShift4Forbid.sign = (-1 : ℤˣ) := by
    simp [frontShift4Forbid, Equiv.Perm.sign_mul, h23, h12, h01]
  simp [h]

private theorem forbidOne_left_rotated
    (l r : Fin 4 ↪ Fin 7)
    (hmatch : frontShift4Forbid.toEmbedding.trans r = l)
    (hrmono : StrictMono (r : Fin 4 → Fin 7)) :
    forbidOneLeft.orient l =
      !(forbidOneLeftSigns (tupleVertices r)) := by
  have hperm : forbidOneLeft.orient (frontShift4Forbid.toEmbedding.trans r) =
      !(forbidOneLeft.orient r) := by
    rw [Hyper.orient_perm]
    simp [frontShift4Forbid_odd]
  calc
    forbidOneLeft.orient l =
        forbidOneLeft.orient (frontShift4Forbid.toEmbedding.trans r) :=
      congrArg forbidOneLeft.orient hmatch.symm
    _ = !(forbidOneLeft.orient r) := hperm
    _ = !(forbidOneLeftSigns (tupleVertices r)) :=
      congrArg (fun b : Bool => !b)
        (fromOrderedSigns_orient_strictMono forbidOneLeftSigns r hrmono)

/-- If an ordinary amalgam existed, these constraints would apply
to all mixed five-tuples. The joint embeddings are defined
intrinsically without choosing an ambient vertex order. -/
private theorem joint_source_facets
    (E : Hyper 4 (Fin 8))
    (hL : Preserves forbidOneLeft E (leftJointInclusion 6))
    (hR : Preserves forbidOneRight E (rightJointInclusion 6))
    (t : Fin 5 ↪ Fin 8) (l r : Fin 4 ↪ Fin 7)
    (hlmap : l.trans (leftJointInclusion 6) = facet t 4)
    (hrmap : r.trans (rightJointInclusion 6) = facet t 0) :
    E.orient (facet t 4) = forbidOneLeft.orient l ∧
    E.orient (facet t 0) = forbidOneRight.orient r := by
  constructor
  · rw [← hlmap]
    exact hL l
  · rw [← hrmap]
    exact hR r

/-- All fifteen mixed four-tuple signs in the order required by
the Boolean certificate: 12,13,14,15,23,24,25,34,35,45,
then 01,02,03,04,05. -/
private def forbidOneBits (E : Hyper 4 (Fin 8)) : Fin 15 → Bool :=
  ![E.orient pair12, E.orient pair13, E.orient pair14, E.orient pair15, E.orient pair23, E.orient pair24, E.orient pair25, E.orient pair34, E.orient pair35, E.orient pair45, E.orient pair01, E.orient pair02, E.orient pair03, E.orient pair04, E.orient pair05]

/-- No eight-vertex four-hypertournament can amalgamate the
chosen one-point extensions while avoiding T_{4,1}. -/
theorem forbidOne_no_joint
    (E : Hyper 4 (Fin 8))
    (hE : Admissible ({0,2} : Set ℕ) E)
    (hL : Preserves forbidOneLeft E (leftJointInclusion 6))
    (hR : Preserves forbidOneRight E (rightJointInclusion 6)) : False := by
  have h012 : ruleCm (E.orient pair01) (E.orient pair02) (E.orient pair12) = true := by
    have hmaps := joint_source_facets E hL hR frame012 left012 right012
      (by ext x; fin_cases x <;> decide)
      (by ext x; fin_cases x <;> decide)
    have halpha : forbidOneLeft.orient left012 = false := by
      calc
        forbidOneLeft.orient left012 =
            !(forbidOneLeftSigns (tupleVertices right012)) :=
          forbidOne_left_rotated left012 right012
            (by ext x; fin_cases x <;> decide) (by decide)
        _ = false := by decide
    have hbeta : forbidOneRight.orient right012 = false := by
      calc
        forbidOneRight.orient right012 =
            forbidOneRightSigns (tupleVertices right012) :=
          fromOrderedSigns_orient_strictMono forbidOneRightSigns right012
            (by decide)
        _ = false := by decide
    have hendL : E.orient (facet frame012 4) = false :=
      hmaps.1.trans halpha
    have hendR : E.orient (facet frame012 0) = false :=
      hmaps.2.trans hbeta
    have hpacket := ruleCm_of_allowed_mixed E frame012 (hE frame012)
      hendL hendR
    have e1 : facet frame012 3 = pair01 := by
      ext x; fin_cases x <;> decide
    have e2 : facet frame012 2 = pair02 := by
      ext x; fin_cases x <;> decide
    have e3 : facet frame012 1 = pair12 := by
      ext x; fin_cases x <;> decide
    simpa only [e1, e2, e3] using hpacket
  have h013 : ruleT (E.orient pair01) (E.orient pair03) (E.orient pair13) = true := by
    have hmaps := joint_source_facets E hL hR frame013 left013 right013
      (by ext x; fin_cases x <;> decide)
      (by ext x; fin_cases x <;> decide)
    have halpha : forbidOneLeft.orient left013 = false := by
      calc
        forbidOneLeft.orient left013 =
            !(forbidOneLeftSigns (tupleVertices right013)) :=
          forbidOne_left_rotated left013 right013
            (by ext x; fin_cases x <;> decide) (by decide)
        _ = false := by decide
    have hbeta : forbidOneRight.orient right013 = true := by
      calc
        forbidOneRight.orient right013 =
            forbidOneRightSigns (tupleVertices right013) :=
          fromOrderedSigns_orient_strictMono forbidOneRightSigns right013
            (by decide)
        _ = true := by decide
    have hendL : E.orient (facet frame013 4) = false :=
      hmaps.1.trans halpha
    have hendR : E.orient (facet frame013 0) = true :=
      hmaps.2.trans hbeta
    have hpacket := ruleT_of_allowed_mixed E frame013 (hE frame013)
      (by rw [hendL, hendR]; decide)
    have e1 : facet frame013 3 = pair01 := by
      ext x; fin_cases x <;> decide
    have e2 : facet frame013 2 = pair03 := by
      ext x; fin_cases x <;> decide
    have e3 : facet frame013 1 = pair13 := by
      ext x; fin_cases x <;> decide
    simpa only [e1, e2, e3] using hpacket
  have h014 : ruleT (E.orient pair01) (E.orient pair04) (E.orient pair14) = true := by
    have hmaps := joint_source_facets E hL hR frame014 left014 right014
      (by ext x; fin_cases x <;> decide)
      (by ext x; fin_cases x <;> decide)
    have halpha : forbidOneLeft.orient left014 = false := by
      calc
        forbidOneLeft.orient left014 =
            !(forbidOneLeftSigns (tupleVertices right014)) :=
          forbidOne_left_rotated left014 right014
            (by ext x; fin_cases x <;> decide) (by decide)
        _ = false := by decide
    have hbeta : forbidOneRight.orient right014 = true := by
      calc
        forbidOneRight.orient right014 =
            forbidOneRightSigns (tupleVertices right014) :=
          fromOrderedSigns_orient_strictMono forbidOneRightSigns right014
            (by decide)
        _ = true := by decide
    have hendL : E.orient (facet frame014 4) = false :=
      hmaps.1.trans halpha
    have hendR : E.orient (facet frame014 0) = true :=
      hmaps.2.trans hbeta
    have hpacket := ruleT_of_allowed_mixed E frame014 (hE frame014)
      (by rw [hendL, hendR]; decide)
    have e1 : facet frame014 3 = pair01 := by
      ext x; fin_cases x <;> decide
    have e2 : facet frame014 2 = pair04 := by
      ext x; fin_cases x <;> decide
    have e3 : facet frame014 1 = pair14 := by
      ext x; fin_cases x <;> decide
    simpa only [e1, e2, e3] using hpacket
  have h015 : ruleT (E.orient pair01) (E.orient pair05) (E.orient pair15) = true := by
    have hmaps := joint_source_facets E hL hR frame015 left015 right015
      (by ext x; fin_cases x <;> decide)
      (by ext x; fin_cases x <;> decide)
    have halpha : forbidOneLeft.orient left015 = false := by
      calc
        forbidOneLeft.orient left015 =
            !(forbidOneLeftSigns (tupleVertices right015)) :=
          forbidOne_left_rotated left015 right015
            (by ext x; fin_cases x <;> decide) (by decide)
        _ = false := by decide
    have hbeta : forbidOneRight.orient right015 = true := by
      calc
        forbidOneRight.orient right015 =
            forbidOneRightSigns (tupleVertices right015) :=
          fromOrderedSigns_orient_strictMono forbidOneRightSigns right015
            (by decide)
        _ = true := by decide
    have hendL : E.orient (facet frame015 4) = false :=
      hmaps.1.trans halpha
    have hendR : E.orient (facet frame015 0) = true :=
      hmaps.2.trans hbeta
    have hpacket := ruleT_of_allowed_mixed E frame015 (hE frame015)
      (by rw [hendL, hendR]; decide)
    have e1 : facet frame015 3 = pair01 := by
      ext x; fin_cases x <;> decide
    have e2 : facet frame015 2 = pair05 := by
      ext x; fin_cases x <;> decide
    have e3 : facet frame015 1 = pair15 := by
      ext x; fin_cases x <;> decide
    simpa only [e1, e2, e3] using hpacket
  have h023 : ruleT (E.orient pair02) (E.orient pair03) (E.orient pair23) = true := by
    have hmaps := joint_source_facets E hL hR frame023 left023 right023
      (by ext x; fin_cases x <;> decide)
      (by ext x; fin_cases x <;> decide)
    have halpha : forbidOneLeft.orient left023 = false := by
      calc
        forbidOneLeft.orient left023 =
            !(forbidOneLeftSigns (tupleVertices right023)) :=
          forbidOne_left_rotated left023 right023
            (by ext x; fin_cases x <;> decide) (by decide)
        _ = false := by decide
    have hbeta : forbidOneRight.orient right023 = true := by
      calc
        forbidOneRight.orient right023 =
            forbidOneRightSigns (tupleVertices right023) :=
          fromOrderedSigns_orient_strictMono forbidOneRightSigns right023
            (by decide)
        _ = true := by decide
    have hendL : E.orient (facet frame023 4) = false :=
      hmaps.1.trans halpha
    have hendR : E.orient (facet frame023 0) = true :=
      hmaps.2.trans hbeta
    have hpacket := ruleT_of_allowed_mixed E frame023 (hE frame023)
      (by rw [hendL, hendR]; decide)
    have e1 : facet frame023 3 = pair02 := by
      ext x; fin_cases x <;> decide
    have e2 : facet frame023 2 = pair03 := by
      ext x; fin_cases x <;> decide
    have e3 : facet frame023 1 = pair23 := by
      ext x; fin_cases x <;> decide
    simpa only [e1, e2, e3] using hpacket
  have h024 : ruleT (E.orient pair02) (E.orient pair04) (E.orient pair24) = true := by
    have hmaps := joint_source_facets E hL hR frame024 left024 right024
      (by ext x; fin_cases x <;> decide)
      (by ext x; fin_cases x <;> decide)
    have halpha : forbidOneLeft.orient left024 = false := by
      calc
        forbidOneLeft.orient left024 =
            !(forbidOneLeftSigns (tupleVertices right024)) :=
          forbidOne_left_rotated left024 right024
            (by ext x; fin_cases x <;> decide) (by decide)
        _ = false := by decide
    have hbeta : forbidOneRight.orient right024 = true := by
      calc
        forbidOneRight.orient right024 =
            forbidOneRightSigns (tupleVertices right024) :=
          fromOrderedSigns_orient_strictMono forbidOneRightSigns right024
            (by decide)
        _ = true := by decide
    have hendL : E.orient (facet frame024 4) = false :=
      hmaps.1.trans halpha
    have hendR : E.orient (facet frame024 0) = true :=
      hmaps.2.trans hbeta
    have hpacket := ruleT_of_allowed_mixed E frame024 (hE frame024)
      (by rw [hendL, hendR]; decide)
    have e1 : facet frame024 3 = pair02 := by
      ext x; fin_cases x <;> decide
    have e2 : facet frame024 2 = pair04 := by
      ext x; fin_cases x <;> decide
    have e3 : facet frame024 1 = pair24 := by
      ext x; fin_cases x <;> decide
    simpa only [e1, e2, e3] using hpacket
  have h025 : ruleT (E.orient pair02) (E.orient pair05) (E.orient pair25) = true := by
    have hmaps := joint_source_facets E hL hR frame025 left025 right025
      (by ext x; fin_cases x <;> decide)
      (by ext x; fin_cases x <;> decide)
    have halpha : forbidOneLeft.orient left025 = false := by
      calc
        forbidOneLeft.orient left025 =
            !(forbidOneLeftSigns (tupleVertices right025)) :=
          forbidOne_left_rotated left025 right025
            (by ext x; fin_cases x <;> decide) (by decide)
        _ = false := by decide
    have hbeta : forbidOneRight.orient right025 = true := by
      calc
        forbidOneRight.orient right025 =
            forbidOneRightSigns (tupleVertices right025) :=
          fromOrderedSigns_orient_strictMono forbidOneRightSigns right025
            (by decide)
        _ = true := by decide
    have hendL : E.orient (facet frame025 4) = false :=
      hmaps.1.trans halpha
    have hendR : E.orient (facet frame025 0) = true :=
      hmaps.2.trans hbeta
    have hpacket := ruleT_of_allowed_mixed E frame025 (hE frame025)
      (by rw [hendL, hendR]; decide)
    have e1 : facet frame025 3 = pair02 := by
      ext x; fin_cases x <;> decide
    have e2 : facet frame025 2 = pair05 := by
      ext x; fin_cases x <;> decide
    have e3 : facet frame025 1 = pair25 := by
      ext x; fin_cases x <;> decide
    simpa only [e1, e2, e3] using hpacket
  have h034 : ruleCm (E.orient pair03) (E.orient pair04) (E.orient pair34) = true := by
    have hmaps := joint_source_facets E hL hR frame034 left034 right034
      (by ext x; fin_cases x <;> decide)
      (by ext x; fin_cases x <;> decide)
    have halpha : forbidOneLeft.orient left034 = false := by
      calc
        forbidOneLeft.orient left034 =
            !(forbidOneLeftSigns (tupleVertices right034)) :=
          forbidOne_left_rotated left034 right034
            (by ext x; fin_cases x <;> decide) (by decide)
        _ = false := by decide
    have hbeta : forbidOneRight.orient right034 = false := by
      calc
        forbidOneRight.orient right034 =
            forbidOneRightSigns (tupleVertices right034) :=
          fromOrderedSigns_orient_strictMono forbidOneRightSigns right034
            (by decide)
        _ = false := by decide
    have hendL : E.orient (facet frame034 4) = false :=
      hmaps.1.trans halpha
    have hendR : E.orient (facet frame034 0) = false :=
      hmaps.2.trans hbeta
    have hpacket := ruleCm_of_allowed_mixed E frame034 (hE frame034)
      hendL hendR
    have e1 : facet frame034 3 = pair03 := by
      ext x; fin_cases x <;> decide
    have e2 : facet frame034 2 = pair04 := by
      ext x; fin_cases x <;> decide
    have e3 : facet frame034 1 = pair34 := by
      ext x; fin_cases x <;> decide
    simpa only [e1, e2, e3] using hpacket
  have h035 : ruleT (E.orient pair03) (E.orient pair05) (E.orient pair35) = true := by
    have hmaps := joint_source_facets E hL hR frame035 left035 right035
      (by ext x; fin_cases x <;> decide)
      (by ext x; fin_cases x <;> decide)
    have halpha : forbidOneLeft.orient left035 = true := by
      calc
        forbidOneLeft.orient left035 =
            !(forbidOneLeftSigns (tupleVertices right035)) :=
          forbidOne_left_rotated left035 right035
            (by ext x; fin_cases x <;> decide) (by decide)
        _ = true := by decide
    have hbeta : forbidOneRight.orient right035 = false := by
      calc
        forbidOneRight.orient right035 =
            forbidOneRightSigns (tupleVertices right035) :=
          fromOrderedSigns_orient_strictMono forbidOneRightSigns right035
            (by decide)
        _ = false := by decide
    have hendL : E.orient (facet frame035 4) = true :=
      hmaps.1.trans halpha
    have hendR : E.orient (facet frame035 0) = false :=
      hmaps.2.trans hbeta
    have hpacket := ruleT_of_allowed_mixed E frame035 (hE frame035)
      (by rw [hendL, hendR]; decide)
    have e1 : facet frame035 3 = pair03 := by
      ext x; fin_cases x <;> decide
    have e2 : facet frame035 2 = pair05 := by
      ext x; fin_cases x <;> decide
    have e3 : facet frame035 1 = pair35 := by
      ext x; fin_cases x <;> decide
    simpa only [e1, e2, e3] using hpacket
  have h045 : ruleCm (E.orient pair04) (E.orient pair05) (E.orient pair45) = true := by
    have hmaps := joint_source_facets E hL hR frame045 left045 right045
      (by ext x; fin_cases x <;> decide)
      (by ext x; fin_cases x <;> decide)
    have halpha : forbidOneLeft.orient left045 = false := by
      calc
        forbidOneLeft.orient left045 =
            !(forbidOneLeftSigns (tupleVertices right045)) :=
          forbidOne_left_rotated left045 right045
            (by ext x; fin_cases x <;> decide) (by decide)
        _ = false := by decide
    have hbeta : forbidOneRight.orient right045 = false := by
      calc
        forbidOneRight.orient right045 =
            forbidOneRightSigns (tupleVertices right045) :=
          fromOrderedSigns_orient_strictMono forbidOneRightSigns right045
            (by decide)
        _ = false := by decide
    have hendL : E.orient (facet frame045 4) = false :=
      hmaps.1.trans halpha
    have hendR : E.orient (facet frame045 0) = false :=
      hmaps.2.trans hbeta
    have hpacket := ruleCm_of_allowed_mixed E frame045 (hE frame045)
      hendL hendR
    have e1 : facet frame045 3 = pair04 := by
      ext x; fin_cases x <;> decide
    have e2 : facet frame045 2 = pair05 := by
      ext x; fin_cases x <;> decide
    have e3 : facet frame045 1 = pair45 := by
      ext x; fin_cases x <;> decide
    simpa only [e1, e2, e3] using hpacket
  have h123 : ruleT (E.orient pair12) (E.orient pair13) (E.orient pair23) = true := by
    have hmaps := joint_source_facets E hL hR frame123 left123 right123
      (by ext x; fin_cases x <;> decide)
      (by ext x; fin_cases x <;> decide)
    have halpha : forbidOneLeft.orient left123 = false := by
      calc
        forbidOneLeft.orient left123 =
            !(forbidOneLeftSigns (tupleVertices right123)) :=
          forbidOne_left_rotated left123 right123
            (by ext x; fin_cases x <;> decide) (by decide)
        _ = false := by decide
    have hbeta : forbidOneRight.orient right123 = true := by
      calc
        forbidOneRight.orient right123 =
            forbidOneRightSigns (tupleVertices right123) :=
          fromOrderedSigns_orient_strictMono forbidOneRightSigns right123
            (by decide)
        _ = true := by decide
    have hendL : E.orient (facet frame123 4) = false :=
      hmaps.1.trans halpha
    have hendR : E.orient (facet frame123 0) = true :=
      hmaps.2.trans hbeta
    have hpacket := ruleT_of_allowed_mixed E frame123 (hE frame123)
      (by rw [hendL, hendR]; decide)
    have e1 : facet frame123 3 = pair12 := by
      ext x; fin_cases x <;> decide
    have e2 : facet frame123 2 = pair13 := by
      ext x; fin_cases x <;> decide
    have e3 : facet frame123 1 = pair23 := by
      ext x; fin_cases x <;> decide
    simpa only [e1, e2, e3] using hpacket
  have h124 : ruleT (E.orient pair12) (E.orient pair14) (E.orient pair24) = true := by
    have hmaps := joint_source_facets E hL hR frame124 left124 right124
      (by ext x; fin_cases x <;> decide)
      (by ext x; fin_cases x <;> decide)
    have halpha : forbidOneLeft.orient left124 = false := by
      calc
        forbidOneLeft.orient left124 =
            !(forbidOneLeftSigns (tupleVertices right124)) :=
          forbidOne_left_rotated left124 right124
            (by ext x; fin_cases x <;> decide) (by decide)
        _ = false := by decide
    have hbeta : forbidOneRight.orient right124 = true := by
      calc
        forbidOneRight.orient right124 =
            forbidOneRightSigns (tupleVertices right124) :=
          fromOrderedSigns_orient_strictMono forbidOneRightSigns right124
            (by decide)
        _ = true := by decide
    have hendL : E.orient (facet frame124 4) = false :=
      hmaps.1.trans halpha
    have hendR : E.orient (facet frame124 0) = true :=
      hmaps.2.trans hbeta
    have hpacket := ruleT_of_allowed_mixed E frame124 (hE frame124)
      (by rw [hendL, hendR]; decide)
    have e1 : facet frame124 3 = pair12 := by
      ext x; fin_cases x <;> decide
    have e2 : facet frame124 2 = pair14 := by
      ext x; fin_cases x <;> decide
    have e3 : facet frame124 1 = pair24 := by
      ext x; fin_cases x <;> decide
    simpa only [e1, e2, e3] using hpacket
  have h125 : ruleT (E.orient pair12) (E.orient pair15) (E.orient pair25) = true := by
    have hmaps := joint_source_facets E hL hR frame125 left125 right125
      (by ext x; fin_cases x <;> decide)
      (by ext x; fin_cases x <;> decide)
    have halpha : forbidOneLeft.orient left125 = false := by
      calc
        forbidOneLeft.orient left125 =
            !(forbidOneLeftSigns (tupleVertices right125)) :=
          forbidOne_left_rotated left125 right125
            (by ext x; fin_cases x <;> decide) (by decide)
        _ = false := by decide
    have hbeta : forbidOneRight.orient right125 = true := by
      calc
        forbidOneRight.orient right125 =
            forbidOneRightSigns (tupleVertices right125) :=
          fromOrderedSigns_orient_strictMono forbidOneRightSigns right125
            (by decide)
        _ = true := by decide
    have hendL : E.orient (facet frame125 4) = false :=
      hmaps.1.trans halpha
    have hendR : E.orient (facet frame125 0) = true :=
      hmaps.2.trans hbeta
    have hpacket := ruleT_of_allowed_mixed E frame125 (hE frame125)
      (by rw [hendL, hendR]; decide)
    have e1 : facet frame125 3 = pair12 := by
      ext x; fin_cases x <;> decide
    have e2 : facet frame125 2 = pair15 := by
      ext x; fin_cases x <;> decide
    have e3 : facet frame125 1 = pair25 := by
      ext x; fin_cases x <;> decide
    simpa only [e1, e2, e3] using hpacket
  have h134 : ruleCm (E.orient pair13) (E.orient pair14) (E.orient pair34) = true := by
    have hmaps := joint_source_facets E hL hR frame134 left134 right134
      (by ext x; fin_cases x <;> decide)
      (by ext x; fin_cases x <;> decide)
    have halpha : forbidOneLeft.orient left134 = false := by
      calc
        forbidOneLeft.orient left134 =
            !(forbidOneLeftSigns (tupleVertices right134)) :=
          forbidOne_left_rotated left134 right134
            (by ext x; fin_cases x <;> decide) (by decide)
        _ = false := by decide
    have hbeta : forbidOneRight.orient right134 = false := by
      calc
        forbidOneRight.orient right134 =
            forbidOneRightSigns (tupleVertices right134) :=
          fromOrderedSigns_orient_strictMono forbidOneRightSigns right134
            (by decide)
        _ = false := by decide
    have hendL : E.orient (facet frame134 4) = false :=
      hmaps.1.trans halpha
    have hendR : E.orient (facet frame134 0) = false :=
      hmaps.2.trans hbeta
    have hpacket := ruleCm_of_allowed_mixed E frame134 (hE frame134)
      hendL hendR
    have e1 : facet frame134 3 = pair13 := by
      ext x; fin_cases x <;> decide
    have e2 : facet frame134 2 = pair14 := by
      ext x; fin_cases x <;> decide
    have e3 : facet frame134 1 = pair34 := by
      ext x; fin_cases x <;> decide
    simpa only [e1, e2, e3] using hpacket
  have h135 : ruleCp (E.orient pair13) (E.orient pair15) (E.orient pair35) = true := by
    have hmaps := joint_source_facets E hL hR frame135 left135 right135
      (by ext x; fin_cases x <;> decide)
      (by ext x; fin_cases x <;> decide)
    have halpha : forbidOneLeft.orient left135 = true := by
      calc
        forbidOneLeft.orient left135 =
            !(forbidOneLeftSigns (tupleVertices right135)) :=
          forbidOne_left_rotated left135 right135
            (by ext x; fin_cases x <;> decide) (by decide)
        _ = true := by decide
    have hbeta : forbidOneRight.orient right135 = true := by
      calc
        forbidOneRight.orient right135 =
            forbidOneRightSigns (tupleVertices right135) :=
          fromOrderedSigns_orient_strictMono forbidOneRightSigns right135
            (by decide)
        _ = true := by decide
    have hendL : E.orient (facet frame135 4) = true :=
      hmaps.1.trans halpha
    have hendR : E.orient (facet frame135 0) = true :=
      hmaps.2.trans hbeta
    have hpacket := ruleCp_of_allowed_mixed E frame135 (hE frame135)
      hendL hendR
    have e1 : facet frame135 3 = pair13 := by
      ext x; fin_cases x <;> decide
    have e2 : facet frame135 2 = pair15 := by
      ext x; fin_cases x <;> decide
    have e3 : facet frame135 1 = pair35 := by
      ext x; fin_cases x <;> decide
    simpa only [e1, e2, e3] using hpacket
  have h145 : ruleT (E.orient pair14) (E.orient pair15) (E.orient pair45) = true := by
    have hmaps := joint_source_facets E hL hR frame145 left145 right145
      (by ext x; fin_cases x <;> decide)
      (by ext x; fin_cases x <;> decide)
    have halpha : forbidOneLeft.orient left145 = false := by
      calc
        forbidOneLeft.orient left145 =
            !(forbidOneLeftSigns (tupleVertices right145)) :=
          forbidOne_left_rotated left145 right145
            (by ext x; fin_cases x <;> decide) (by decide)
        _ = false := by decide
    have hbeta : forbidOneRight.orient right145 = true := by
      calc
        forbidOneRight.orient right145 =
            forbidOneRightSigns (tupleVertices right145) :=
          fromOrderedSigns_orient_strictMono forbidOneRightSigns right145
            (by decide)
        _ = true := by decide
    have hendL : E.orient (facet frame145 4) = false :=
      hmaps.1.trans halpha
    have hendR : E.orient (facet frame145 0) = true :=
      hmaps.2.trans hbeta
    have hpacket := ruleT_of_allowed_mixed E frame145 (hE frame145)
      (by rw [hendL, hendR]; decide)
    have e1 : facet frame145 3 = pair14 := by
      ext x; fin_cases x <;> decide
    have e2 : facet frame145 2 = pair15 := by
      ext x; fin_cases x <;> decide
    have e3 : facet frame145 1 = pair45 := by
      ext x; fin_cases x <;> decide
    simpa only [e1, e2, e3] using hpacket
  have h234 : ruleT (E.orient pair23) (E.orient pair24) (E.orient pair34) = true := by
    have hmaps := joint_source_facets E hL hR frame234 left234 right234
      (by ext x; fin_cases x <;> decide)
      (by ext x; fin_cases x <;> decide)
    have halpha : forbidOneLeft.orient left234 = false := by
      calc
        forbidOneLeft.orient left234 =
            !(forbidOneLeftSigns (tupleVertices right234)) :=
          forbidOne_left_rotated left234 right234
            (by ext x; fin_cases x <;> decide) (by decide)
        _ = false := by decide
    have hbeta : forbidOneRight.orient right234 = true := by
      calc
        forbidOneRight.orient right234 =
            forbidOneRightSigns (tupleVertices right234) :=
          fromOrderedSigns_orient_strictMono forbidOneRightSigns right234
            (by decide)
        _ = true := by decide
    have hendL : E.orient (facet frame234 4) = false :=
      hmaps.1.trans halpha
    have hendR : E.orient (facet frame234 0) = true :=
      hmaps.2.trans hbeta
    have hpacket := ruleT_of_allowed_mixed E frame234 (hE frame234)
      (by rw [hendL, hendR]; decide)
    have e1 : facet frame234 3 = pair23 := by
      ext x; fin_cases x <;> decide
    have e2 : facet frame234 2 = pair24 := by
      ext x; fin_cases x <;> decide
    have e3 : facet frame234 1 = pair34 := by
      ext x; fin_cases x <;> decide
    simpa only [e1, e2, e3] using hpacket
  have h235 : ruleCp (E.orient pair23) (E.orient pair25) (E.orient pair35) = true := by
    have hmaps := joint_source_facets E hL hR frame235 left235 right235
      (by ext x; fin_cases x <;> decide)
      (by ext x; fin_cases x <;> decide)
    have halpha : forbidOneLeft.orient left235 = true := by
      calc
        forbidOneLeft.orient left235 =
            !(forbidOneLeftSigns (tupleVertices right235)) :=
          forbidOne_left_rotated left235 right235
            (by ext x; fin_cases x <;> decide) (by decide)
        _ = true := by decide
    have hbeta : forbidOneRight.orient right235 = true := by
      calc
        forbidOneRight.orient right235 =
            forbidOneRightSigns (tupleVertices right235) :=
          fromOrderedSigns_orient_strictMono forbidOneRightSigns right235
            (by decide)
        _ = true := by decide
    have hendL : E.orient (facet frame235 4) = true :=
      hmaps.1.trans halpha
    have hendR : E.orient (facet frame235 0) = true :=
      hmaps.2.trans hbeta
    have hpacket := ruleCp_of_allowed_mixed E frame235 (hE frame235)
      hendL hendR
    have e1 : facet frame235 3 = pair23 := by
      ext x; fin_cases x <;> decide
    have e2 : facet frame235 2 = pair25 := by
      ext x; fin_cases x <;> decide
    have e3 : facet frame235 1 = pair35 := by
      ext x; fin_cases x <;> decide
    simpa only [e1, e2, e3] using hpacket
  have h245 : ruleCm (E.orient pair24) (E.orient pair25) (E.orient pair45) = true := by
    have hmaps := joint_source_facets E hL hR frame245 left245 right245
      (by ext x; fin_cases x <;> decide)
      (by ext x; fin_cases x <;> decide)
    have halpha : forbidOneLeft.orient left245 = false := by
      calc
        forbidOneLeft.orient left245 =
            !(forbidOneLeftSigns (tupleVertices right245)) :=
          forbidOne_left_rotated left245 right245
            (by ext x; fin_cases x <;> decide) (by decide)
        _ = false := by decide
    have hbeta : forbidOneRight.orient right245 = false := by
      calc
        forbidOneRight.orient right245 =
            forbidOneRightSigns (tupleVertices right245) :=
          fromOrderedSigns_orient_strictMono forbidOneRightSigns right245
            (by decide)
        _ = false := by decide
    have hendL : E.orient (facet frame245 4) = false :=
      hmaps.1.trans halpha
    have hendR : E.orient (facet frame245 0) = false :=
      hmaps.2.trans hbeta
    have hpacket := ruleCm_of_allowed_mixed E frame245 (hE frame245)
      hendL hendR
    have e1 : facet frame245 3 = pair24 := by
      ext x; fin_cases x <;> decide
    have e2 : facet frame245 2 = pair25 := by
      ext x; fin_cases x <;> decide
    have e3 : facet frame245 1 = pair45 := by
      ext x; fin_cases x <;> decide
    simpa only [e1, e2, e3] using hpacket
  have h345 : ruleT (E.orient pair34) (E.orient pair35) (E.orient pair45) = true := by
    have hmaps := joint_source_facets E hL hR frame345 left345 right345
      (by ext x; fin_cases x <;> decide)
      (by ext x; fin_cases x <;> decide)
    have halpha : forbidOneLeft.orient left345 = true := by
      calc
        forbidOneLeft.orient left345 =
            !(forbidOneLeftSigns (tupleVertices right345)) :=
          forbidOne_left_rotated left345 right345
            (by ext x; fin_cases x <;> decide) (by decide)
        _ = true := by decide
    have hbeta : forbidOneRight.orient right345 = false := by
      calc
        forbidOneRight.orient right345 =
            forbidOneRightSigns (tupleVertices right345) :=
          fromOrderedSigns_orient_strictMono forbidOneRightSigns right345
            (by decide)
        _ = false := by decide
    have hendL : E.orient (facet frame345 4) = true :=
      hmaps.1.trans halpha
    have hendR : E.orient (facet frame345 0) = false :=
      hmaps.2.trans hbeta
    have hpacket := ruleT_of_allowed_mixed E frame345 (hE frame345)
      (by rw [hendL, hendR]; decide)
    have e1 : facet frame345 3 = pair34 := by
      ext x; fin_cases x <;> decide
    have e2 : facet frame345 2 = pair35 := by
      ext x; fin_cases x <;> decide
    have e3 : facet frame345 1 = pair45 := by
      ext x; fin_cases x <;> decide
    simpa only [e1, e2, e3] using hpacket
  have htop : rawTopOk (forbidOneBits E) = true := by
    simp [rawTopOk, forbidOneBits, h123, h124, h125, h134, h135, h145, h234, h235, h245, h345]
  have houter : rawOuterOk (forbidOneBits E) = true := by
    simp [rawOuterOk, forbidOneBits, h012, h013, h014, h015, h023, h024, h025, h034, h035, h045]
  exact no_raw_forbidOne_assignment (forbidOneBits E) htop houter

/-- Distinct source orientations rule out identifying the two new
vertices in an ordinary amalgam. -/
theorem forbidOne_disagreement :
    ∃ t : Fin 4 ↪ Fin 7,
      forbidOneLeft.orient t ≠ forbidOneRight.orient t := by
  refine ⟨right012, ?_⟩
  have hm : StrictMono (right012 : Fin 4 → Fin 7) := by decide
  change (Hyper.fromOrderedSigns forbidOneLeftSigns).orient right012 ≠
    (Hyper.fromOrderedSigns forbidOneRightSigns).orient right012
  rw [fromOrderedSigns_orient_strictMono forbidOneLeftSigns right012 hm,
    fromOrderedSigns_orient_strictMono forbidOneRightSigns right012 hm]
  decide

/-- Second arity-four negative seed, including ordinary amalgamation:
the class omitting local type T_{4,1} fails AP. -/
theorem forbidOneFour_not_hasAP :
    ¬ HasAP 4 ({0,2} : Set ℕ) := by
  apply not_hasAP_of_no_joint
    forbidOneBase forbidOneLeft forbidOneRight
    forbidOne_base_admissible forbidOne_left_admissible
    forbidOne_right_admissible forbidOne_base_left forbidOne_base_right
    forbidOne_disagreement
  intro E hE hL hR
  exact forbidOne_no_joint E hE hL hR

end Hypertournaments
