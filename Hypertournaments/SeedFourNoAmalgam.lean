import Hypertournaments.OnePointJoint
import Hypertournaments.SeedFourAdmissible
import Hypertournaments.SeedFourPacketBridge

/-!
# Complete ordinary-AP obstruction for the central-only four-hypertournament age

The seven triples are exactly those in the AI technical note. We
derive their packet constraints from intrinsic orientations, then
invoke the previously kernel-checked seven-rule Boolean contradiction.

No brute-force search over possible nine-vertex completions is used.
-/

namespace Hypertournaments

set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

private def pair01 : Fin 4 ↪ Fin 9 := ⟨![7,0,1,8], by decide⟩
private def pair02 : Fin 4 ↪ Fin 9 := ⟨![7,0,2,8], by decide⟩
private def pair03 : Fin 4 ↪ Fin 9 := ⟨![7,0,3,8], by decide⟩
private def pair04 : Fin 4 ↪ Fin 9 := ⟨![7,0,4,8], by decide⟩
private def pair06 : Fin 4 ↪ Fin 9 := ⟨![7,0,6,8], by decide⟩
private def pair12 : Fin 4 ↪ Fin 9 := ⟨![7,1,2,8], by decide⟩
private def pair14 : Fin 4 ↪ Fin 9 := ⟨![7,1,4,8], by decide⟩
private def pair15 : Fin 4 ↪ Fin 9 := ⟨![7,1,5,8], by decide⟩
private def pair23 : Fin 4 ↪ Fin 9 := ⟨![7,2,3,8], by decide⟩
private def pair36 : Fin 4 ↪ Fin 9 := ⟨![7,3,6,8], by decide⟩
private def pair45 : Fin 4 ↪ Fin 9 := ⟨![7,4,5,8], by decide⟩
private def pair46 : Fin 4 ↪ Fin 9 := ⟨![7,4,6,8], by decide⟩
private def pair56 : Fin 4 ↪ Fin 9 := ⟨![7,5,6,8], by decide⟩

private def frame012 : Fin 5 ↪ Fin 9 := ⟨![7,0,1,2,8], by decide⟩
private def left012 : Fin 4 ↪ Fin 8 := ⟨![7,0,1,2], by decide⟩
private def right012 : Fin 4 ↪ Fin 8 := ⟨![0,1,2,7], by decide⟩
private def frame014 : Fin 5 ↪ Fin 9 := ⟨![7,0,1,4,8], by decide⟩
private def left014 : Fin 4 ↪ Fin 8 := ⟨![7,0,1,4], by decide⟩
private def right014 : Fin 4 ↪ Fin 8 := ⟨![0,1,4,7], by decide⟩
private def frame023 : Fin 5 ↪ Fin 9 := ⟨![7,0,2,3,8], by decide⟩
private def left023 : Fin 4 ↪ Fin 8 := ⟨![7,0,2,3], by decide⟩
private def right023 : Fin 4 ↪ Fin 8 := ⟨![0,2,3,7], by decide⟩
private def frame036 : Fin 5 ↪ Fin 9 := ⟨![7,0,3,6,8], by decide⟩
private def left036 : Fin 4 ↪ Fin 8 := ⟨![7,0,3,6], by decide⟩
private def right036 : Fin 4 ↪ Fin 8 := ⟨![0,3,6,7], by decide⟩
private def frame046 : Fin 5 ↪ Fin 9 := ⟨![7,0,4,6,8], by decide⟩
private def left046 : Fin 4 ↪ Fin 8 := ⟨![7,0,4,6], by decide⟩
private def right046 : Fin 4 ↪ Fin 8 := ⟨![0,4,6,7], by decide⟩
private def frame145 : Fin 5 ↪ Fin 9 := ⟨![7,1,4,5,8], by decide⟩
private def left145 : Fin 4 ↪ Fin 8 := ⟨![7,1,4,5], by decide⟩
private def right145 : Fin 4 ↪ Fin 8 := ⟨![1,4,5,7], by decide⟩
private def frame456 : Fin 5 ↪ Fin 9 := ⟨![7,4,5,6,8], by decide⟩
private def left456 : Fin 4 ↪ Fin 8 := ⟨![7,4,5,6], by decide⟩
private def right456 : Fin 4 ↪ Fin 8 := ⟨![4,5,6,7], by decide⟩

/-- Moving the final coordinate of a four-tuple to the front
is an odd permutation; using this avoids computing a sorting
permutation on every source link. -/
private def frontShift4 : Equiv.Perm (Fin 4) :=
  (Equiv.swap (2 : Fin 4) 3) *
    (Equiv.swap (1 : Fin 4) 2) *
    (Equiv.swap (0 : Fin 4) 1)

private theorem frontShift4_odd :
    frontShift4.sign ≠ (1 : ℤˣ) := by
  have h23 : (Equiv.swap (2 : Fin 4) 3).sign = (-1 : ℤˣ) :=
    Equiv.Perm.sign_swap (by decide)
  have h12 : (Equiv.swap (1 : Fin 4) 2).sign = (-1 : ℤˣ) :=
    Equiv.Perm.sign_swap (by decide)
  have h01 : (Equiv.swap (0 : Fin 4) 1).sign = (-1 : ℤˣ) :=
    Equiv.Perm.sign_swap (by decide)
  have h : frontShift4.sign = (-1 : ℤˣ) := by
    simp [frontShift4, Equiv.Perm.sign_mul, h23, h12, h01]
  simp [h]

private theorem seed4_left_rotated
    (l r : Fin 4 ↪ Fin 8)
    (hmatch : frontShift4.toEmbedding.trans r = l)
    (hrmono : StrictMono (r : Fin 4 → Fin 8)) :
    seed4Left.orient l =
      !(seed4LeftSigns (tupleVertices r)) := by
  have hperm : seed4Left.orient (frontShift4.toEmbedding.trans r) =
      !(seed4Left.orient r) := by
    rw [Hyper.orient_perm]
    simp [frontShift4_odd]
  calc
    seed4Left.orient l =
        seed4Left.orient (frontShift4.toEmbedding.trans r) :=
      congrArg seed4Left.orient hmatch.symm
    _ = !(seed4Left.orient r) := hperm
    _ = !(seed4LeftSigns (tupleVertices r)) :=
      congrArg (!) (fromOrderedSigns_orient_strictMono seed4LeftSigns r hrmono)

private theorem negative_joint_rule
    (E : Hyper 4 (Fin 9))
    (hE : Admissible ({2} : Set ℕ) E)
    (hL : Preserves seed4Left E (leftJointInclusion 7))
    (hR : Preserves seed4Right E (rightJointInclusion 7))
    (t : Fin 5 ↪ Fin 9) (l r : Fin 4 ↪ Fin 8)
    (hlmap : l.trans (leftJointInclusion 7) = facet t 4)
    (hrmap : r.trans (rightJointInclusion 7) = facet t 0)
    (hlbool : seed4Left.orient l = false)
    (hrbool : seed4Right.orient r = false) :
    negativePacketRule
      (E.orient (facet t 3))
      (E.orient (facet t 2))
      (E.orient (facet t 1)) := by
  have hc : localIndex E t = 2 := by simpa using hE t
  have ha : E.orient (facet t 4) = false := by
    rw [← hlmap, hL l]
    exact hlbool
  have hb : E.orient (facet t 0) = false := by
    rw [← hrmap, hR r]
    exact hrbool
  exact negativePacketRule_of_localIndex E t ha hb hc

private theorem positive_joint_rule
    (E : Hyper 4 (Fin 9))
    (hE : Admissible ({2} : Set ℕ) E)
    (hL : Preserves seed4Left E (leftJointInclusion 7))
    (hR : Preserves seed4Right E (rightJointInclusion 7))
    (t : Fin 5 ↪ Fin 9) (l r : Fin 4 ↪ Fin 8)
    (hlmap : l.trans (leftJointInclusion 7) = facet t 4)
    (hrmap : r.trans (rightJointInclusion 7) = facet t 0)
    (hlbool : seed4Left.orient l = true)
    (hrbool : seed4Right.orient r = true) :
    positivePacketRule
      (E.orient (facet t 3))
      (E.orient (facet t 2))
      (E.orient (facet t 1)) := by
  have hc : localIndex E t = 2 := by simpa using hE t
  have ha : E.orient (facet t 4) = true := by
    rw [← hlmap, hL l]
    exact hlbool
  have hb : E.orient (facet t 0) = true := by
    rw [← hrmap, hR r]
    exact hrbool
  exact positivePacketRule_of_localIndex E t ha hb hc

/-- No central-only four-hypertournament on the canonical nine
vertices can simultaneously contain both chosen one-point sides. -/
theorem seed4_no_joint
    (E : Hyper 4 (Fin 9))
    (hE : Admissible ({2} : Set ℕ) E)
    (hL : Preserves seed4Left E (leftJointInclusion 7))
    (hR : Preserves seed4Right E (rightJointInclusion 7)) : False := by
  have h012 : negativePacketRule (E.orient pair01) (E.orient pair02) (E.orient pair12) := by
    have h := negative_joint_rule E hE hL hR frame012 left012 right012
      (by ext x; fin_cases x <;> decide)
      (by ext x; fin_cases x <;> decide)
      (by
        calc
          seed4Left.orient left012 =
              !(seed4LeftSigns (tupleVertices right012)) :=
            seed4_left_rotated left012 right012
              (by ext x; fin_cases x <;> decide) (by decide)
          _ = false := by decide)
      (by
        calc
          seed4Right.orient right012 =
              seed4RightSigns (tupleVertices right012) :=
            fromOrderedSigns_orient_strictMono seed4RightSigns right012
              (by decide)
          _ = false := by decide)
    have e₁ : facet frame012 3 = pair01 := by ext x; fin_cases x <;> decide
    have e₂ : facet frame012 2 = pair02 := by ext x; fin_cases x <;> decide
    have e₃ : facet frame012 1 = pair12 := by ext x; fin_cases x <;> decide
    simpa only [e₁, e₂, e₃] using h
  have h014 : positivePacketRule (E.orient pair01) (E.orient pair04) (E.orient pair14) := by
    have h := positive_joint_rule E hE hL hR frame014 left014 right014
      (by ext x; fin_cases x <;> decide)
      (by ext x; fin_cases x <;> decide)
      (by
        calc
          seed4Left.orient left014 =
              !(seed4LeftSigns (tupleVertices right014)) :=
            seed4_left_rotated left014 right014
              (by ext x; fin_cases x <;> decide) (by decide)
          _ = true := by decide)
      (by
        calc
          seed4Right.orient right014 =
              seed4RightSigns (tupleVertices right014) :=
            fromOrderedSigns_orient_strictMono seed4RightSigns right014
              (by decide)
          _ = true := by decide)
    have e₁ : facet frame014 3 = pair01 := by ext x; fin_cases x <;> decide
    have e₂ : facet frame014 2 = pair04 := by ext x; fin_cases x <;> decide
    have e₃ : facet frame014 1 = pair14 := by ext x; fin_cases x <;> decide
    simpa only [e₁, e₂, e₃] using h
  have h023 : negativePacketRule (E.orient pair02) (E.orient pair03) (E.orient pair23) := by
    have h := negative_joint_rule E hE hL hR frame023 left023 right023
      (by ext x; fin_cases x <;> decide)
      (by ext x; fin_cases x <;> decide)
      (by
        calc
          seed4Left.orient left023 =
              !(seed4LeftSigns (tupleVertices right023)) :=
            seed4_left_rotated left023 right023
              (by ext x; fin_cases x <;> decide) (by decide)
          _ = false := by decide)
      (by
        calc
          seed4Right.orient right023 =
              seed4RightSigns (tupleVertices right023) :=
            fromOrderedSigns_orient_strictMono seed4RightSigns right023
              (by decide)
          _ = false := by decide)
    have e₁ : facet frame023 3 = pair02 := by ext x; fin_cases x <;> decide
    have e₂ : facet frame023 2 = pair03 := by ext x; fin_cases x <;> decide
    have e₃ : facet frame023 1 = pair23 := by ext x; fin_cases x <;> decide
    simpa only [e₁, e₂, e₃] using h
  have h036 : negativePacketRule (E.orient pair03) (E.orient pair06) (E.orient pair36) := by
    have h := negative_joint_rule E hE hL hR frame036 left036 right036
      (by ext x; fin_cases x <;> decide)
      (by ext x; fin_cases x <;> decide)
      (by
        calc
          seed4Left.orient left036 =
              !(seed4LeftSigns (tupleVertices right036)) :=
            seed4_left_rotated left036 right036
              (by ext x; fin_cases x <;> decide) (by decide)
          _ = false := by decide)
      (by
        calc
          seed4Right.orient right036 =
              seed4RightSigns (tupleVertices right036) :=
            fromOrderedSigns_orient_strictMono seed4RightSigns right036
              (by decide)
          _ = false := by decide)
    have e₁ : facet frame036 3 = pair03 := by ext x; fin_cases x <;> decide
    have e₂ : facet frame036 2 = pair06 := by ext x; fin_cases x <;> decide
    have e₃ : facet frame036 1 = pair36 := by ext x; fin_cases x <;> decide
    simpa only [e₁, e₂, e₃] using h
  have h046 : positivePacketRule (E.orient pair04) (E.orient pair06) (E.orient pair46) := by
    have h := positive_joint_rule E hE hL hR frame046 left046 right046
      (by ext x; fin_cases x <;> decide)
      (by ext x; fin_cases x <;> decide)
      (by
        calc
          seed4Left.orient left046 =
              !(seed4LeftSigns (tupleVertices right046)) :=
            seed4_left_rotated left046 right046
              (by ext x; fin_cases x <;> decide) (by decide)
          _ = true := by decide)
      (by
        calc
          seed4Right.orient right046 =
              seed4RightSigns (tupleVertices right046) :=
            fromOrderedSigns_orient_strictMono seed4RightSigns right046
              (by decide)
          _ = true := by decide)
    have e₁ : facet frame046 3 = pair04 := by ext x; fin_cases x <;> decide
    have e₂ : facet frame046 2 = pair06 := by ext x; fin_cases x <;> decide
    have e₃ : facet frame046 1 = pair46 := by ext x; fin_cases x <;> decide
    simpa only [e₁, e₂, e₃] using h
  have h145 : negativePacketRule (E.orient pair14) (E.orient pair15) (E.orient pair45) := by
    have h := negative_joint_rule E hE hL hR frame145 left145 right145
      (by ext x; fin_cases x <;> decide)
      (by ext x; fin_cases x <;> decide)
      (by
        calc
          seed4Left.orient left145 =
              !(seed4LeftSigns (tupleVertices right145)) :=
            seed4_left_rotated left145 right145
              (by ext x; fin_cases x <;> decide) (by decide)
          _ = false := by decide)
      (by
        calc
          seed4Right.orient right145 =
              seed4RightSigns (tupleVertices right145) :=
            fromOrderedSigns_orient_strictMono seed4RightSigns right145
              (by decide)
          _ = false := by decide)
    have e₁ : facet frame145 3 = pair14 := by ext x; fin_cases x <;> decide
    have e₂ : facet frame145 2 = pair15 := by ext x; fin_cases x <;> decide
    have e₃ : facet frame145 1 = pair45 := by ext x; fin_cases x <;> decide
    simpa only [e₁, e₂, e₃] using h
  have h456 : positivePacketRule (E.orient pair45) (E.orient pair46) (E.orient pair56) := by
    have h := positive_joint_rule E hE hL hR frame456 left456 right456
      (by ext x; fin_cases x <;> decide)
      (by ext x; fin_cases x <;> decide)
      (by
        calc
          seed4Left.orient left456 =
              !(seed4LeftSigns (tupleVertices right456)) :=
            seed4_left_rotated left456 right456
              (by ext x; fin_cases x <;> decide) (by decide)
          _ = true := by decide)
      (by
        calc
          seed4Right.orient right456 =
              seed4RightSigns (tupleVertices right456) :=
            fromOrderedSigns_orient_strictMono seed4RightSigns right456
              (by decide)
          _ = true := by decide)
    have e₁ : facet frame456 3 = pair45 := by ext x; fin_cases x <;> decide
    have e₂ : facet frame456 2 = pair46 := by ext x; fin_cases x <;> decide
    have e₃ : facet frame456 1 = pair56 := by ext x; fin_cases x <;> decide
    simpa only [e₁, e₂, e₃] using h
  exact arityFour_central_seed_rules_unsatisfiable
    (E.orient pair01) (E.orient pair02) (E.orient pair03)
    (E.orient pair04) (E.orient pair06) (E.orient pair12)
    (E.orient pair14) (E.orient pair15) (E.orient pair23)
    (E.orient pair36) (E.orient pair45) (E.orient pair46)
    (E.orient pair56)
    h012 h014 h023 h036 h046 h145 h456

/-- An ordinary amalgam cannot identify the left and right new
vertices: the source links disagree on an explicit four-tuple. -/
theorem seed4_disagreement :
    ∃ t : Fin 4 ↪ Fin 8, seed4Left.orient t ≠ seed4Right.orient t := by
  refine ⟨right012, ?_⟩
  have hm : StrictMono (right012 : Fin 4 → Fin 8) := by decide
  change (Hyper.fromOrderedSigns seed4LeftSigns).orient right012 ≠
    (Hyper.fromOrderedSigns seed4RightSigns).orient right012
  rw [fromOrderedSigns_orient_strictMono seed4LeftSigns right012 hm,
    fromOrderedSigns_orient_strictMono seed4RightSigns right012 hm]
  decide

/-- First nontrivial negative seed: central-only four-hypertournaments
fail ordinary amalgamation (not merely strong amalgamation). -/
theorem centralOnlyFour_not_hasAP :
    ¬ HasAP 4 ({2} : Set ℕ) := by
  apply not_hasAP_of_no_joint
    seed4Base seed4Left seed4Right
    seed4_base_admissible seed4_left_admissible seed4_right_admissible
    seed4_base_left seed4_base_right seed4_disagreement
  intro E hE hL hR
  exact seed4_no_joint E hE hL hR

end Hypertournaments
