import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FinCases
import Hypertournaments.SeedFiveConePacketBridge
import Hypertournaments.OnePointJoint
import Hypertournaments.SeedFourLogic

/-!
# Complete ordinary AP obstruction for the central-only five-hypertournament age

The concrete cone span is kernel-certified in SeedFiveConeData.  Its
mixed six-facet packets recover the seven implication constraints of
the established arity-four central-only obstruction.

The argument avoids constructing an entire lower-arity hypertournament:
it reads the thirteen common-cone five-facet orientations and applies
the existing seven-rule contradiction. The two source extensions
disagree on a specified common-cone five-tuple, so ordinary amalgams
cannot identify the new vertices.

No new axioms, placeholders, external SAT assumptions or source
amalgamation hypotheses are used.
-/

namespace Hypertournaments

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

private def conePair01 : Fin 5 ↪ Fin 10 := ⟨![0,8,1,2,9], by decide⟩
private def conePair02 : Fin 5 ↪ Fin 10 := ⟨![0,8,1,3,9], by decide⟩
private def conePair03 : Fin 5 ↪ Fin 10 := ⟨![0,8,1,4,9], by decide⟩
private def conePair04 : Fin 5 ↪ Fin 10 := ⟨![0,8,1,5,9], by decide⟩
private def conePair06 : Fin 5 ↪ Fin 10 := ⟨![0,8,1,7,9], by decide⟩
private def conePair12 : Fin 5 ↪ Fin 10 := ⟨![0,8,2,3,9], by decide⟩
private def conePair14 : Fin 5 ↪ Fin 10 := ⟨![0,8,2,5,9], by decide⟩
private def conePair15 : Fin 5 ↪ Fin 10 := ⟨![0,8,2,6,9], by decide⟩
private def conePair23 : Fin 5 ↪ Fin 10 := ⟨![0,8,3,4,9], by decide⟩
private def conePair36 : Fin 5 ↪ Fin 10 := ⟨![0,8,4,7,9], by decide⟩
private def conePair45 : Fin 5 ↪ Fin 10 := ⟨![0,8,5,6,9], by decide⟩
private def conePair46 : Fin 5 ↪ Fin 10 := ⟨![0,8,5,7,9], by decide⟩
private def conePair56 : Fin 5 ↪ Fin 10 := ⟨![0,8,6,7,9], by decide⟩

private def coneFrame012 : Fin 6 ↪ Fin 10 := ⟨![0,8,1,2,3,9], by decide⟩
private def coneLeft012 : Fin 5 ↪ Fin 9 := ⟨![0,8,1,2,3], by decide⟩
private def coneRight012 : Fin 5 ↪ Fin 9 := ⟨![0,1,2,3,8], by decide⟩
private def coneFrame014 : Fin 6 ↪ Fin 10 := ⟨![0,8,1,2,5,9], by decide⟩
private def coneLeft014 : Fin 5 ↪ Fin 9 := ⟨![0,8,1,2,5], by decide⟩
private def coneRight014 : Fin 5 ↪ Fin 9 := ⟨![0,1,2,5,8], by decide⟩
private def coneFrame023 : Fin 6 ↪ Fin 10 := ⟨![0,8,1,3,4,9], by decide⟩
private def coneLeft023 : Fin 5 ↪ Fin 9 := ⟨![0,8,1,3,4], by decide⟩
private def coneRight023 : Fin 5 ↪ Fin 9 := ⟨![0,1,3,4,8], by decide⟩
private def coneFrame036 : Fin 6 ↪ Fin 10 := ⟨![0,8,1,4,7,9], by decide⟩
private def coneLeft036 : Fin 5 ↪ Fin 9 := ⟨![0,8,1,4,7], by decide⟩
private def coneRight036 : Fin 5 ↪ Fin 9 := ⟨![0,1,4,7,8], by decide⟩
private def coneFrame046 : Fin 6 ↪ Fin 10 := ⟨![0,8,1,5,7,9], by decide⟩
private def coneLeft046 : Fin 5 ↪ Fin 9 := ⟨![0,8,1,5,7], by decide⟩
private def coneRight046 : Fin 5 ↪ Fin 9 := ⟨![0,1,5,7,8], by decide⟩
private def coneFrame145 : Fin 6 ↪ Fin 10 := ⟨![0,8,2,5,6,9], by decide⟩
private def coneLeft145 : Fin 5 ↪ Fin 9 := ⟨![0,8,2,5,6], by decide⟩
private def coneRight145 : Fin 5 ↪ Fin 9 := ⟨![0,2,5,6,8], by decide⟩
private def coneFrame456 : Fin 6 ↪ Fin 10 := ⟨![0,8,5,6,7,9], by decide⟩
private def coneLeft456 : Fin 5 ↪ Fin 9 := ⟨![0,8,5,6,7], by decide⟩
private def coneRight456 : Fin 5 ↪ Fin 9 := ⟨![0,5,6,7,8], by decide⟩

/-- Moving the last source vertex past three old vertices into the
position immediately after the cone vertex is an odd permutation. -/
private def middleShift5 : Equiv.Perm (Fin 5) :=
  (Equiv.swap (3 : Fin 5) 4) *
    (Equiv.swap (2 : Fin 5) 3) *
    (Equiv.swap (1 : Fin 5) 2)

private theorem middleShift5_odd :
    middleShift5.sign ≠ (1 : ℤˣ) := by
  have h34 : (Equiv.swap (3 : Fin 5) 4).sign = (-1 : ℤˣ) :=
    Equiv.Perm.sign_swap (by decide)
  have h23 : (Equiv.swap (2 : Fin 5) 3).sign = (-1 : ℤˣ) :=
    Equiv.Perm.sign_swap (by decide)
  have h12 : (Equiv.swap (1 : Fin 5) 2).sign = (-1 : ℤˣ) :=
    Equiv.Perm.sign_swap (by decide)
  have h : middleShift5.sign = (-1 : ℤˣ) := by
    simp [middleShift5, Equiv.Perm.sign_mul, h34, h23, h12]
  simp [h, Units.ext_iff]

/-- Evaluate a left source link with its new vertex in second position,
without constructing an expensive sorting permutation. -/
private theorem coneLeft_shifted
    (l r : Fin 5 ↪ Fin 9)
    (hmatch : middleShift5.toEmbedding.trans r = l)
    (hrmono : StrictMono (r : Fin 5 → Fin 9)) :
    seed5ConeLeft.orient l =
      !(seed5ConeLeftSigns (tupleVertices r)) := by
  have hp : seed5ConeLeft.orient (middleShift5.toEmbedding.trans r) =
      !(seed5ConeLeft.orient r) := by
    rw [Hyper.orient_perm]
    simp [middleShift5_odd]
  calc
    seed5ConeLeft.orient l =
        seed5ConeLeft.orient (middleShift5.toEmbedding.trans r) :=
      congrArg seed5ConeLeft.orient hmatch.symm
    _ = !(seed5ConeLeft.orient r) := hp
    _ = !(seed5ConeLeftSigns (tupleVertices r)) :=
      congrArg (fun b : Bool => !b)
        (fromOrderedSigns_orient_strictMono seed5ConeLeftSigns r hrmono)

/-- The unknown cone-free facet disappears from the local centrality
condition and leaves the lower-arity negative three-variable rule. -/
private theorem coneNegative_joint_rule
    (E : Hyper 5 (Fin 10))
    (hE : Admissible ({3} : Set ℕ) E)
    (hL : Preserves seed5ConeLeft E (leftJointInclusion 8))
    (hR : Preserves seed5ConeRight E (rightJointInclusion 8))
    (t : Fin 6 ↪ Fin 10) (l r : Fin 5 ↪ Fin 9)
    (hlmap : l.trans (leftJointInclusion 8) = facet t 5)
    (hrmap : r.trans (rightJointInclusion 8) = facet t 1)
    (hlbool : seed5ConeLeft.orient l = false)
    (hrbool : seed5ConeRight.orient r = false) :
    negativePacketRule
      (E.orient (facet t 4))
      (E.orient (facet t 3))
      (E.orient (facet t 2)) := by
  have hc : localIndex E t = 3 := by simpa using hE t
  have ha : E.orient (facet t 5) = false := by
    rw [← hlmap, hL l]
    exact hlbool
  have hb : E.orient (facet t 1) = false := by
    rw [← hrmap, hR r]
    exact hrbool
  exact coneNegativeRule_of_localIndex E t
    (E.orient (facet t 4)) (E.orient (facet t 3))
    (E.orient (facet t 2)) hb rfl rfl rfl ha hc

private theorem conePositive_joint_rule
    (E : Hyper 5 (Fin 10))
    (hE : Admissible ({3} : Set ℕ) E)
    (hL : Preserves seed5ConeLeft E (leftJointInclusion 8))
    (hR : Preserves seed5ConeRight E (rightJointInclusion 8))
    (t : Fin 6 ↪ Fin 10) (l r : Fin 5 ↪ Fin 9)
    (hlmap : l.trans (leftJointInclusion 8) = facet t 5)
    (hrmap : r.trans (rightJointInclusion 8) = facet t 1)
    (hlbool : seed5ConeLeft.orient l = true)
    (hrbool : seed5ConeRight.orient r = true) :
    positivePacketRule
      (E.orient (facet t 4))
      (E.orient (facet t 3))
      (E.orient (facet t 2)) := by
  have hc : localIndex E t = 3 := by simpa using hE t
  have ha : E.orient (facet t 5) = true := by
    rw [← hlmap, hL l]
    exact hlbool
  have hb : E.orient (facet t 1) = true := by
    rw [← hrmap, hR r]
    exact hrbool
  exact conePositiveRule_of_localIndex E t
    (E.orient (facet t 4)) (E.orient (facet t 3))
    (E.orient (facet t 2)) hb rfl rfl rfl ha hc

/-- The cone span cannot be jointly embedded into any central-only
five-hypertournament on the canonical ten vertices. -/
theorem seed5Cone_no_joint
    (E : Hyper 5 (Fin 10))
    (hE : Admissible ({3} : Set ℕ) E)
    (hL : Preserves seed5ConeLeft E (leftJointInclusion 8))
    (hR : Preserves seed5ConeRight E (rightJointInclusion 8)) :
    False := by
  have h012 : negativePacketRule
      (E.orient conePair01) (E.orient conePair02)
      (E.orient conePair12) := by
    have h := coneNegative_joint_rule E hE hL hR
      coneFrame012 coneLeft012 coneRight012
      (by ext x; fin_cases x <;> decide)
      (by ext x; fin_cases x <;> decide)
      (by
        calc
          seed5ConeLeft.orient coneLeft012 =
              !(seed5ConeLeftSigns (tupleVertices coneRight012)) :=
            coneLeft_shifted coneLeft012 coneRight012
              (by ext x; fin_cases x <;> decide) (by decide)
          _ = false := by decide)
      (by
        calc
          seed5ConeRight.orient coneRight012 =
              seed5ConeRightSigns (tupleVertices coneRight012) :=
            fromOrderedSigns_orient_strictMono
              seed5ConeRightSigns coneRight012 (by decide)
          _ = false := by decide)
    have e1 : facet coneFrame012 4 = conePair01 := by
      ext x; fin_cases x <;> decide
    have e2 : facet coneFrame012 3 = conePair02 := by
      ext x; fin_cases x <;> decide
    have e3 : facet coneFrame012 2 = conePair12 := by
      ext x; fin_cases x <;> decide
    simpa only [e1, e2, e3] using h
  have h014 : positivePacketRule
      (E.orient conePair01) (E.orient conePair04)
      (E.orient conePair14) := by
    have h := conePositive_joint_rule E hE hL hR
      coneFrame014 coneLeft014 coneRight014
      (by ext x; fin_cases x <;> decide)
      (by ext x; fin_cases x <;> decide)
      (by
        calc
          seed5ConeLeft.orient coneLeft014 =
              !(seed5ConeLeftSigns (tupleVertices coneRight014)) :=
            coneLeft_shifted coneLeft014 coneRight014
              (by ext x; fin_cases x <;> decide) (by decide)
          _ = true := by decide)
      (by
        calc
          seed5ConeRight.orient coneRight014 =
              seed5ConeRightSigns (tupleVertices coneRight014) :=
            fromOrderedSigns_orient_strictMono
              seed5ConeRightSigns coneRight014 (by decide)
          _ = true := by decide)
    have e1 : facet coneFrame014 4 = conePair01 := by
      ext x; fin_cases x <;> decide
    have e2 : facet coneFrame014 3 = conePair04 := by
      ext x; fin_cases x <;> decide
    have e3 : facet coneFrame014 2 = conePair14 := by
      ext x; fin_cases x <;> decide
    simpa only [e1, e2, e3] using h
  have h023 : negativePacketRule
      (E.orient conePair02) (E.orient conePair03)
      (E.orient conePair23) := by
    have h := coneNegative_joint_rule E hE hL hR
      coneFrame023 coneLeft023 coneRight023
      (by ext x; fin_cases x <;> decide)
      (by ext x; fin_cases x <;> decide)
      (by
        calc
          seed5ConeLeft.orient coneLeft023 =
              !(seed5ConeLeftSigns (tupleVertices coneRight023)) :=
            coneLeft_shifted coneLeft023 coneRight023
              (by ext x; fin_cases x <;> decide) (by decide)
          _ = false := by decide)
      (by
        calc
          seed5ConeRight.orient coneRight023 =
              seed5ConeRightSigns (tupleVertices coneRight023) :=
            fromOrderedSigns_orient_strictMono
              seed5ConeRightSigns coneRight023 (by decide)
          _ = false := by decide)
    have e1 : facet coneFrame023 4 = conePair02 := by
      ext x; fin_cases x <;> decide
    have e2 : facet coneFrame023 3 = conePair03 := by
      ext x; fin_cases x <;> decide
    have e3 : facet coneFrame023 2 = conePair23 := by
      ext x; fin_cases x <;> decide
    simpa only [e1, e2, e3] using h
  have h036 : negativePacketRule
      (E.orient conePair03) (E.orient conePair06)
      (E.orient conePair36) := by
    have h := coneNegative_joint_rule E hE hL hR
      coneFrame036 coneLeft036 coneRight036
      (by ext x; fin_cases x <;> decide)
      (by ext x; fin_cases x <;> decide)
      (by
        calc
          seed5ConeLeft.orient coneLeft036 =
              !(seed5ConeLeftSigns (tupleVertices coneRight036)) :=
            coneLeft_shifted coneLeft036 coneRight036
              (by ext x; fin_cases x <;> decide) (by decide)
          _ = false := by decide)
      (by
        calc
          seed5ConeRight.orient coneRight036 =
              seed5ConeRightSigns (tupleVertices coneRight036) :=
            fromOrderedSigns_orient_strictMono
              seed5ConeRightSigns coneRight036 (by decide)
          _ = false := by decide)
    have e1 : facet coneFrame036 4 = conePair03 := by
      ext x; fin_cases x <;> decide
    have e2 : facet coneFrame036 3 = conePair06 := by
      ext x; fin_cases x <;> decide
    have e3 : facet coneFrame036 2 = conePair36 := by
      ext x; fin_cases x <;> decide
    simpa only [e1, e2, e3] using h
  have h046 : positivePacketRule
      (E.orient conePair04) (E.orient conePair06)
      (E.orient conePair46) := by
    have h := conePositive_joint_rule E hE hL hR
      coneFrame046 coneLeft046 coneRight046
      (by ext x; fin_cases x <;> decide)
      (by ext x; fin_cases x <;> decide)
      (by
        calc
          seed5ConeLeft.orient coneLeft046 =
              !(seed5ConeLeftSigns (tupleVertices coneRight046)) :=
            coneLeft_shifted coneLeft046 coneRight046
              (by ext x; fin_cases x <;> decide) (by decide)
          _ = true := by decide)
      (by
        calc
          seed5ConeRight.orient coneRight046 =
              seed5ConeRightSigns (tupleVertices coneRight046) :=
            fromOrderedSigns_orient_strictMono
              seed5ConeRightSigns coneRight046 (by decide)
          _ = true := by decide)
    have e1 : facet coneFrame046 4 = conePair04 := by
      ext x; fin_cases x <;> decide
    have e2 : facet coneFrame046 3 = conePair06 := by
      ext x; fin_cases x <;> decide
    have e3 : facet coneFrame046 2 = conePair46 := by
      ext x; fin_cases x <;> decide
    simpa only [e1, e2, e3] using h
  have h145 : negativePacketRule
      (E.orient conePair14) (E.orient conePair15)
      (E.orient conePair45) := by
    have h := coneNegative_joint_rule E hE hL hR
      coneFrame145 coneLeft145 coneRight145
      (by ext x; fin_cases x <;> decide)
      (by ext x; fin_cases x <;> decide)
      (by
        calc
          seed5ConeLeft.orient coneLeft145 =
              !(seed5ConeLeftSigns (tupleVertices coneRight145)) :=
            coneLeft_shifted coneLeft145 coneRight145
              (by ext x; fin_cases x <;> decide) (by decide)
          _ = false := by decide)
      (by
        calc
          seed5ConeRight.orient coneRight145 =
              seed5ConeRightSigns (tupleVertices coneRight145) :=
            fromOrderedSigns_orient_strictMono
              seed5ConeRightSigns coneRight145 (by decide)
          _ = false := by decide)
    have e1 : facet coneFrame145 4 = conePair14 := by
      ext x; fin_cases x <;> decide
    have e2 : facet coneFrame145 3 = conePair15 := by
      ext x; fin_cases x <;> decide
    have e3 : facet coneFrame145 2 = conePair45 := by
      ext x; fin_cases x <;> decide
    simpa only [e1, e2, e3] using h
  have h456 : positivePacketRule
      (E.orient conePair45) (E.orient conePair46)
      (E.orient conePair56) := by
    have h := conePositive_joint_rule E hE hL hR
      coneFrame456 coneLeft456 coneRight456
      (by ext x; fin_cases x <;> decide)
      (by ext x; fin_cases x <;> decide)
      (by
        calc
          seed5ConeLeft.orient coneLeft456 =
              !(seed5ConeLeftSigns (tupleVertices coneRight456)) :=
            coneLeft_shifted coneLeft456 coneRight456
              (by ext x; fin_cases x <;> decide) (by decide)
          _ = true := by decide)
      (by
        calc
          seed5ConeRight.orient coneRight456 =
              seed5ConeRightSigns (tupleVertices coneRight456) :=
            fromOrderedSigns_orient_strictMono
              seed5ConeRightSigns coneRight456 (by decide)
          _ = true := by decide)
    have e1 : facet coneFrame456 4 = conePair45 := by
      ext x; fin_cases x <;> decide
    have e2 : facet coneFrame456 3 = conePair46 := by
      ext x; fin_cases x <;> decide
    have e3 : facet coneFrame456 2 = conePair56 := by
      ext x; fin_cases x <;> decide
    simpa only [e1, e2, e3] using h
  exact arityFour_central_seed_rules_unsatisfiable
    (E.orient conePair01) (E.orient conePair02) (E.orient conePair03)
    (E.orient conePair04) (E.orient conePair06) (E.orient conePair12)
    (E.orient conePair14) (E.orient conePair15) (E.orient conePair23)
    (E.orient conePair36) (E.orient conePair45) (E.orient conePair46)
    (E.orient conePair56)
    h012 h014 h023 h036 h046 h145 h456

/-- The left and right coned one-point extensions disagree on a
five-tuple containing the common cone vertex. They cannot identify
their new vertices in an ordinary amalgam. -/
theorem seed5Cone_disagreement :
    ∃ t : Fin 5 ↪ Fin 9,
      seed5ConeLeft.orient t ≠ seed5ConeRight.orient t := by
  let t : Fin 5 ↪ Fin 9 := ⟨![0,1,2,3,8], by decide⟩
  refine ⟨t, ?_⟩
  have hm : StrictMono (t : Fin 5 → Fin 9) := by decide
  change (Hyper.fromOrderedSigns seed5ConeLeftSigns).orient t ≠
    (Hyper.fromOrderedSigns seed5ConeRightSigns).orient t
  rw [fromOrderedSigns_orient_strictMono seed5ConeLeftSigns t hm,
    fromOrderedSigns_orient_strictMono seed5ConeRightSigns t hm]
  decide

/-- The final missing arity-five negative seed: the class allowing
only the central six-vertex local type fails ordinary AP. -/
theorem seed5Cone_not_hasAP :
    ¬ HasAP 5 ({3} : Set ℕ) := by
  apply not_hasAP_of_no_joint
    seed5ConeBase seed5ConeLeft seed5ConeRight
    seed5Cone_base_admissible seed5Cone_left_admissible
    seed5Cone_right_admissible seed5Cone_base_left seed5Cone_base_right
    seed5Cone_disagreement
  intro E hE hL hR
  exact seed5Cone_no_joint E hE hL hR

end Hypertournaments
