import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FinCases
import Hypertournaments.SeedFiveExtraPacketBridge

/-!
# Ordinary non-amalgamation of the exceptional arity-five {0,1,3} class

Each of the nine selected mixed six-packets is represented by an
actual injective tuple and forced into the finite XOR SAT obstruction.
The two new vertices cannot be identified because the side structures
have different orientations on an explicit five-tuple.

All actual source signs are read from *increasing* tables, with the
even four-swap front-rotation used for the left link.
-/

namespace Hypertournaments

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

private def frontShift5Extra : Equiv.Perm (Fin 5) :=
  (Equiv.swap (3 : Fin 5) 4) *
    (Equiv.swap (2 : Fin 5) 3) *
    (Equiv.swap (1 : Fin 5) 2) *
    (Equiv.swap (0 : Fin 5) 1)

private theorem frontShift5Extra_even :
    frontShift5Extra.sign = (1 : ℤˣ) := by
  have h34 : (Equiv.swap (3 : Fin 5) 4).sign = (-1 : ℤˣ) :=
    Equiv.Perm.sign_swap (by decide)
  have h23 : (Equiv.swap (2 : Fin 5) 3).sign = (-1 : ℤˣ) :=
    Equiv.Perm.sign_swap (by decide)
  have h12 : (Equiv.swap (1 : Fin 5) 2).sign = (-1 : ℤˣ) :=
    Equiv.Perm.sign_swap (by decide)
  have h01 : (Equiv.swap (0 : Fin 5) 1).sign = (-1 : ℤˣ) :=
    Equiv.Perm.sign_swap (by decide)
  simp [frontShift5Extra, Equiv.Perm.sign_mul, h34, h23, h12, h01]

private theorem seed5Extra_left_rotated
    (l rr : Fin 5 ↪ Fin 7)
    (hmatch : frontShift5Extra.toEmbedding.trans rr = l)
    (hrmono : StrictMono (rr : Fin 5 → Fin 7)) :
    seed5ExtraLeft.orient l = seed5ExtraLeftSigns (tupleVertices rr) := by
  have hp : seed5ExtraLeft.orient (frontShift5Extra.toEmbedding.trans rr) =
      seed5ExtraLeft.orient rr := by
    rw [Hyper.orient_perm]
    simp [frontShift5Extra_even]
  calc
    seed5ExtraLeft.orient l =
        seed5ExtraLeft.orient (frontShift5Extra.toEmbedding.trans rr) :=
      congrArg seed5ExtraLeft.orient hmatch.symm
    _ = seed5ExtraLeft.orient rr := hp
    _ = seed5ExtraLeftSigns (tupleVertices rr) :=
      fromOrderedSigns_orient_strictMono seed5ExtraLeftSigns rr hrmono

private def mixed012 : Fin 5 ↪ Fin 8 := ⟨![6,0,1,2,7], by decide⟩
private def mixed013 : Fin 5 ↪ Fin 8 := ⟨![6,0,1,3,7], by decide⟩
private def mixed014 : Fin 5 ↪ Fin 8 := ⟨![6,0,1,4,7], by decide⟩
private def mixed015 : Fin 5 ↪ Fin 8 := ⟨![6,0,1,5,7], by decide⟩
private def mixed023 : Fin 5 ↪ Fin 8 := ⟨![6,0,2,3,7], by decide⟩
private def mixed024 : Fin 5 ↪ Fin 8 := ⟨![6,0,2,4,7], by decide⟩
private def mixed025 : Fin 5 ↪ Fin 8 := ⟨![6,0,2,5,7], by decide⟩
private def mixed034 : Fin 5 ↪ Fin 8 := ⟨![6,0,3,4,7], by decide⟩
private def mixed035 : Fin 5 ↪ Fin 8 := ⟨![6,0,3,5,7], by decide⟩
private def mixed045 : Fin 5 ↪ Fin 8 := ⟨![6,0,4,5,7], by decide⟩
private def mixed123 : Fin 5 ↪ Fin 8 := ⟨![6,1,2,3,7], by decide⟩
private def mixed124 : Fin 5 ↪ Fin 8 := ⟨![6,1,2,4,7], by decide⟩
private def mixed125 : Fin 5 ↪ Fin 8 := ⟨![6,1,2,5,7], by decide⟩
private def mixed134 : Fin 5 ↪ Fin 8 := ⟨![6,1,3,4,7], by decide⟩
private def mixed135 : Fin 5 ↪ Fin 8 := ⟨![6,1,3,5,7], by decide⟩
private def mixed145 : Fin 5 ↪ Fin 8 := ⟨![6,1,4,5,7], by decide⟩
private def mixed234 : Fin 5 ↪ Fin 8 := ⟨![6,2,3,4,7], by decide⟩
private def mixed235 : Fin 5 ↪ Fin 8 := ⟨![6,2,3,5,7], by decide⟩
private def mixed245 : Fin 5 ↪ Fin 8 := ⟨![6,2,4,5,7], by decide⟩
private def mixed345 : Fin 5 ↪ Fin 8 := ⟨![6,3,4,5,7], by decide⟩

/-- Twenty actual mixed five-set orientation bits, lexicographically indexed. -/
def seed5ExtraMixedBits (E : Hyper 5 (Fin 8)) : Fin 20 → Bool :=
  ![E.orient mixed012,
    E.orient mixed013,
    E.orient mixed014,
    E.orient mixed015,
    E.orient mixed023,
    E.orient mixed024,
    E.orient mixed025,
    E.orient mixed034,
    E.orient mixed035,
    E.orient mixed045,
    E.orient mixed123,
    E.orient mixed124,
    E.orient mixed125,
    E.orient mixed134,
    E.orient mixed135,
    E.orient mixed145,
    E.orient mixed234,
    E.orient mixed235,
    E.orient mixed245,
    E.orient mixed345]

private def frame0123 : Fin 6 ↪ Fin 8 := ⟨![6,0,1,2,3,7], by decide⟩
private def left0123 : Fin 5 ↪ Fin 7 := ⟨![6,0,1,2,3], by decide⟩
private def right0123 : Fin 5 ↪ Fin 7 := ⟨![0,1,2,3,6], by decide⟩
private def frame0125 : Fin 6 ↪ Fin 8 := ⟨![6,0,1,2,5,7], by decide⟩
private def left0125 : Fin 5 ↪ Fin 7 := ⟨![6,0,1,2,5], by decide⟩
private def right0125 : Fin 5 ↪ Fin 7 := ⟨![0,1,2,5,6], by decide⟩
private def frame0134 : Fin 6 ↪ Fin 8 := ⟨![6,0,1,3,4,7], by decide⟩
private def left0134 : Fin 5 ↪ Fin 7 := ⟨![6,0,1,3,4], by decide⟩
private def right0134 : Fin 5 ↪ Fin 7 := ⟨![0,1,3,4,6], by decide⟩
private def frame0135 : Fin 6 ↪ Fin 8 := ⟨![6,0,1,3,5,7], by decide⟩
private def left0135 : Fin 5 ↪ Fin 7 := ⟨![6,0,1,3,5], by decide⟩
private def right0135 : Fin 5 ↪ Fin 7 := ⟨![0,1,3,5,6], by decide⟩
private def frame0145 : Fin 6 ↪ Fin 8 := ⟨![6,0,1,4,5,7], by decide⟩
private def left0145 : Fin 5 ↪ Fin 7 := ⟨![6,0,1,4,5], by decide⟩
private def right0145 : Fin 5 ↪ Fin 7 := ⟨![0,1,4,5,6], by decide⟩
private def frame0235 : Fin 6 ↪ Fin 8 := ⟨![6,0,2,3,5,7], by decide⟩
private def left0235 : Fin 5 ↪ Fin 7 := ⟨![6,0,2,3,5], by decide⟩
private def right0235 : Fin 5 ↪ Fin 7 := ⟨![0,2,3,5,6], by decide⟩
private def frame0345 : Fin 6 ↪ Fin 8 := ⟨![6,0,3,4,5,7], by decide⟩
private def left0345 : Fin 5 ↪ Fin 7 := ⟨![6,0,3,4,5], by decide⟩
private def right0345 : Fin 5 ↪ Fin 7 := ⟨![0,3,4,5,6], by decide⟩
private def frame1235 : Fin 6 ↪ Fin 8 := ⟨![6,1,2,3,5,7], by decide⟩
private def left1235 : Fin 5 ↪ Fin 7 := ⟨![6,1,2,3,5], by decide⟩
private def right1235 : Fin 5 ↪ Fin 7 := ⟨![1,2,3,5,6], by decide⟩
private def frame1345 : Fin 6 ↪ Fin 8 := ⟨![6,1,3,4,5,7], by decide⟩
private def left1345 : Fin 5 ↪ Fin 7 := ⟨![6,1,3,4,5], by decide⟩
private def right1345 : Fin 5 ↪ Fin 7 := ⟨![1,3,4,5,6], by decide⟩

/-- Exact local XOR rule on the mixed six-packet 0123. -/
private theorem mixedRule0123
    (E : Hyper 5 (Fin 8))
    (hE : Admissible ({0,1,3} : Set ℕ) E)
    (hL : Preserves seed5ExtraLeft E (leftJointInclusion 6))
    (hR : Preserves seed5ExtraRight E (rightJointInclusion 6)) :
    seed5ExtraRuleSame ((seed5ExtraMixedBits E) 0) ((seed5ExtraMixedBits E) 1) ((seed5ExtraMixedBits E) 4) ((seed5ExtraMixedBits E) 10) := by
  have h0 : E.orient (facet frame0123 0) = false := by
    calc
      E.orient (facet frame0123 0) =
          E.orient (right0123.trans (rightJointInclusion 6)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5ExtraRight.orient right0123 := hR right0123
      _ = false := by
        have hm : StrictMono (right0123 : Fin 5 → Fin 7) := by decide
        change (Hyper.fromOrderedSigns seed5ExtraRightSigns).orient right0123 = false
        rw [fromOrderedSigns_orient_strictMono seed5ExtraRightSigns right0123 hm]
        decide
  have h5 : E.orient (facet frame0123 5) = false := by
    calc
      E.orient (facet frame0123 5) =
          E.orient (left0123.trans (leftJointInclusion 6)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5ExtraLeft.orient left0123 := hL left0123
      _ = false := by
        calc
          seed5ExtraLeft.orient left0123 =
              seed5ExtraLeftSigns (tupleVertices right0123) :=
            seed5Extra_left_rotated left0123 right0123
              (by ext i; fin_cases i <;> decide) (by decide)
          _ = false := by decide
  have h1 : E.orient (facet frame0123 1) = E.orient mixed123 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h2 : E.orient (facet frame0123 2) = E.orient mixed023 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h3 : E.orient (facet frame0123 3) = E.orient mixed013 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h4 : E.orient (facet frame0123 4) = E.orient mixed012 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have hrule : seed5ExtraMixedRule false false
      (E.orient mixed012) (E.orient mixed013) (E.orient mixed023) (E.orient mixed123) :=
    seed5ExtraMixedRule_of_admissible E frame0123 false false
      (E.orient mixed012) (E.orient mixed013) (E.orient mixed023) (E.orient mixed123)
      h0 h1 h2 h3 h4 h5 (hE frame0123)
  change seed5ExtraRuleSame (E.orient mixed012) (E.orient mixed013) (E.orient mixed023) (E.orient mixed123)
  simpa [seed5ExtraMixedRule] using hrule

/-- Exact local XOR rule on the mixed six-packet 0125. -/
private theorem mixedRule0125
    (E : Hyper 5 (Fin 8))
    (hE : Admissible ({0,1,3} : Set ℕ) E)
    (hL : Preserves seed5ExtraLeft E (leftJointInclusion 6))
    (hR : Preserves seed5ExtraRight E (rightJointInclusion 6)) :
    seed5ExtraRuleSame ((seed5ExtraMixedBits E) 0) ((seed5ExtraMixedBits E) 3) ((seed5ExtraMixedBits E) 6) ((seed5ExtraMixedBits E) 12) := by
  have h0 : E.orient (facet frame0125 0) = true := by
    calc
      E.orient (facet frame0125 0) =
          E.orient (right0125.trans (rightJointInclusion 6)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5ExtraRight.orient right0125 := hR right0125
      _ = true := by
        have hm : StrictMono (right0125 : Fin 5 → Fin 7) := by decide
        change (Hyper.fromOrderedSigns seed5ExtraRightSigns).orient right0125 = true
        rw [fromOrderedSigns_orient_strictMono seed5ExtraRightSigns right0125 hm]
        decide
  have h5 : E.orient (facet frame0125 5) = true := by
    calc
      E.orient (facet frame0125 5) =
          E.orient (left0125.trans (leftJointInclusion 6)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5ExtraLeft.orient left0125 := hL left0125
      _ = true := by
        calc
          seed5ExtraLeft.orient left0125 =
              seed5ExtraLeftSigns (tupleVertices right0125) :=
            seed5Extra_left_rotated left0125 right0125
              (by ext i; fin_cases i <;> decide) (by decide)
          _ = true := by decide
  have h1 : E.orient (facet frame0125 1) = E.orient mixed125 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h2 : E.orient (facet frame0125 2) = E.orient mixed025 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h3 : E.orient (facet frame0125 3) = E.orient mixed015 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h4 : E.orient (facet frame0125 4) = E.orient mixed012 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have hrule : seed5ExtraMixedRule true true
      (E.orient mixed012) (E.orient mixed015) (E.orient mixed025) (E.orient mixed125) :=
    seed5ExtraMixedRule_of_admissible E frame0125 true true
      (E.orient mixed012) (E.orient mixed015) (E.orient mixed025) (E.orient mixed125)
      h0 h1 h2 h3 h4 h5 (hE frame0125)
  change seed5ExtraRuleSame (E.orient mixed012) (E.orient mixed015) (E.orient mixed025) (E.orient mixed125)
  simpa [seed5ExtraMixedRule] using hrule

/-- Exact local XOR rule on the mixed six-packet 0134. -/
private theorem mixedRule0134
    (E : Hyper 5 (Fin 8))
    (hE : Admissible ({0,1,3} : Set ℕ) E)
    (hL : Preserves seed5ExtraLeft E (leftJointInclusion 6))
    (hR : Preserves seed5ExtraRight E (rightJointInclusion 6)) :
    seed5ExtraRuleOneZero ((seed5ExtraMixedBits E) 1) ((seed5ExtraMixedBits E) 2) ((seed5ExtraMixedBits E) 7) ((seed5ExtraMixedBits E) 13) := by
  have h0 : E.orient (facet frame0134 0) = true := by
    calc
      E.orient (facet frame0134 0) =
          E.orient (right0134.trans (rightJointInclusion 6)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5ExtraRight.orient right0134 := hR right0134
      _ = true := by
        have hm : StrictMono (right0134 : Fin 5 → Fin 7) := by decide
        change (Hyper.fromOrderedSigns seed5ExtraRightSigns).orient right0134 = true
        rw [fromOrderedSigns_orient_strictMono seed5ExtraRightSigns right0134 hm]
        decide
  have h5 : E.orient (facet frame0134 5) = false := by
    calc
      E.orient (facet frame0134 5) =
          E.orient (left0134.trans (leftJointInclusion 6)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5ExtraLeft.orient left0134 := hL left0134
      _ = false := by
        calc
          seed5ExtraLeft.orient left0134 =
              seed5ExtraLeftSigns (tupleVertices right0134) :=
            seed5Extra_left_rotated left0134 right0134
              (by ext i; fin_cases i <;> decide) (by decide)
          _ = false := by decide
  have h1 : E.orient (facet frame0134 1) = E.orient mixed134 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h2 : E.orient (facet frame0134 2) = E.orient mixed034 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h3 : E.orient (facet frame0134 3) = E.orient mixed014 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h4 : E.orient (facet frame0134 4) = E.orient mixed013 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have hrule : seed5ExtraMixedRule true false
      (E.orient mixed013) (E.orient mixed014) (E.orient mixed034) (E.orient mixed134) :=
    seed5ExtraMixedRule_of_admissible E frame0134 true false
      (E.orient mixed013) (E.orient mixed014) (E.orient mixed034) (E.orient mixed134)
      h0 h1 h2 h3 h4 h5 (hE frame0134)
  change seed5ExtraRuleOneZero (E.orient mixed013) (E.orient mixed014) (E.orient mixed034) (E.orient mixed134)
  simpa [seed5ExtraMixedRule] using hrule

/-- Exact local XOR rule on the mixed six-packet 0135. -/
private theorem mixedRule0135
    (E : Hyper 5 (Fin 8))
    (hE : Admissible ({0,1,3} : Set ℕ) E)
    (hL : Preserves seed5ExtraLeft E (leftJointInclusion 6))
    (hR : Preserves seed5ExtraRight E (rightJointInclusion 6)) :
    seed5ExtraRuleZeroOne ((seed5ExtraMixedBits E) 1) ((seed5ExtraMixedBits E) 3) ((seed5ExtraMixedBits E) 8) ((seed5ExtraMixedBits E) 14) := by
  have h0 : E.orient (facet frame0135 0) = false := by
    calc
      E.orient (facet frame0135 0) =
          E.orient (right0135.trans (rightJointInclusion 6)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5ExtraRight.orient right0135 := hR right0135
      _ = false := by
        have hm : StrictMono (right0135 : Fin 5 → Fin 7) := by decide
        change (Hyper.fromOrderedSigns seed5ExtraRightSigns).orient right0135 = false
        rw [fromOrderedSigns_orient_strictMono seed5ExtraRightSigns right0135 hm]
        decide
  have h5 : E.orient (facet frame0135 5) = true := by
    calc
      E.orient (facet frame0135 5) =
          E.orient (left0135.trans (leftJointInclusion 6)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5ExtraLeft.orient left0135 := hL left0135
      _ = true := by
        calc
          seed5ExtraLeft.orient left0135 =
              seed5ExtraLeftSigns (tupleVertices right0135) :=
            seed5Extra_left_rotated left0135 right0135
              (by ext i; fin_cases i <;> decide) (by decide)
          _ = true := by decide
  have h1 : E.orient (facet frame0135 1) = E.orient mixed135 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h2 : E.orient (facet frame0135 2) = E.orient mixed035 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h3 : E.orient (facet frame0135 3) = E.orient mixed015 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h4 : E.orient (facet frame0135 4) = E.orient mixed013 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have hrule : seed5ExtraMixedRule false true
      (E.orient mixed013) (E.orient mixed015) (E.orient mixed035) (E.orient mixed135) :=
    seed5ExtraMixedRule_of_admissible E frame0135 false true
      (E.orient mixed013) (E.orient mixed015) (E.orient mixed035) (E.orient mixed135)
      h0 h1 h2 h3 h4 h5 (hE frame0135)
  change seed5ExtraRuleZeroOne (E.orient mixed013) (E.orient mixed015) (E.orient mixed035) (E.orient mixed135)
  simpa [seed5ExtraMixedRule] using hrule

/-- Exact local XOR rule on the mixed six-packet 0145. -/
private theorem mixedRule0145
    (E : Hyper 5 (Fin 8))
    (hE : Admissible ({0,1,3} : Set ℕ) E)
    (hL : Preserves seed5ExtraLeft E (leftJointInclusion 6))
    (hR : Preserves seed5ExtraRight E (rightJointInclusion 6)) :
    seed5ExtraRuleSame ((seed5ExtraMixedBits E) 2) ((seed5ExtraMixedBits E) 3) ((seed5ExtraMixedBits E) 9) ((seed5ExtraMixedBits E) 15) := by
  have h0 : E.orient (facet frame0145 0) = false := by
    calc
      E.orient (facet frame0145 0) =
          E.orient (right0145.trans (rightJointInclusion 6)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5ExtraRight.orient right0145 := hR right0145
      _ = false := by
        have hm : StrictMono (right0145 : Fin 5 → Fin 7) := by decide
        change (Hyper.fromOrderedSigns seed5ExtraRightSigns).orient right0145 = false
        rw [fromOrderedSigns_orient_strictMono seed5ExtraRightSigns right0145 hm]
        decide
  have h5 : E.orient (facet frame0145 5) = false := by
    calc
      E.orient (facet frame0145 5) =
          E.orient (left0145.trans (leftJointInclusion 6)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5ExtraLeft.orient left0145 := hL left0145
      _ = false := by
        calc
          seed5ExtraLeft.orient left0145 =
              seed5ExtraLeftSigns (tupleVertices right0145) :=
            seed5Extra_left_rotated left0145 right0145
              (by ext i; fin_cases i <;> decide) (by decide)
          _ = false := by decide
  have h1 : E.orient (facet frame0145 1) = E.orient mixed145 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h2 : E.orient (facet frame0145 2) = E.orient mixed045 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h3 : E.orient (facet frame0145 3) = E.orient mixed015 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h4 : E.orient (facet frame0145 4) = E.orient mixed014 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have hrule : seed5ExtraMixedRule false false
      (E.orient mixed014) (E.orient mixed015) (E.orient mixed045) (E.orient mixed145) :=
    seed5ExtraMixedRule_of_admissible E frame0145 false false
      (E.orient mixed014) (E.orient mixed015) (E.orient mixed045) (E.orient mixed145)
      h0 h1 h2 h3 h4 h5 (hE frame0145)
  change seed5ExtraRuleSame (E.orient mixed014) (E.orient mixed015) (E.orient mixed045) (E.orient mixed145)
  simpa [seed5ExtraMixedRule] using hrule

/-- Exact local XOR rule on the mixed six-packet 0235. -/
private theorem mixedRule0235
    (E : Hyper 5 (Fin 8))
    (hE : Admissible ({0,1,3} : Set ℕ) E)
    (hL : Preserves seed5ExtraLeft E (leftJointInclusion 6))
    (hR : Preserves seed5ExtraRight E (rightJointInclusion 6)) :
    seed5ExtraRuleSame ((seed5ExtraMixedBits E) 4) ((seed5ExtraMixedBits E) 6) ((seed5ExtraMixedBits E) 8) ((seed5ExtraMixedBits E) 17) := by
  have h0 : E.orient (facet frame0235 0) = true := by
    calc
      E.orient (facet frame0235 0) =
          E.orient (right0235.trans (rightJointInclusion 6)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5ExtraRight.orient right0235 := hR right0235
      _ = true := by
        have hm : StrictMono (right0235 : Fin 5 → Fin 7) := by decide
        change (Hyper.fromOrderedSigns seed5ExtraRightSigns).orient right0235 = true
        rw [fromOrderedSigns_orient_strictMono seed5ExtraRightSigns right0235 hm]
        decide
  have h5 : E.orient (facet frame0235 5) = true := by
    calc
      E.orient (facet frame0235 5) =
          E.orient (left0235.trans (leftJointInclusion 6)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5ExtraLeft.orient left0235 := hL left0235
      _ = true := by
        calc
          seed5ExtraLeft.orient left0235 =
              seed5ExtraLeftSigns (tupleVertices right0235) :=
            seed5Extra_left_rotated left0235 right0235
              (by ext i; fin_cases i <;> decide) (by decide)
          _ = true := by decide
  have h1 : E.orient (facet frame0235 1) = E.orient mixed235 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h2 : E.orient (facet frame0235 2) = E.orient mixed035 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h3 : E.orient (facet frame0235 3) = E.orient mixed025 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h4 : E.orient (facet frame0235 4) = E.orient mixed023 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have hrule : seed5ExtraMixedRule true true
      (E.orient mixed023) (E.orient mixed025) (E.orient mixed035) (E.orient mixed235) :=
    seed5ExtraMixedRule_of_admissible E frame0235 true true
      (E.orient mixed023) (E.orient mixed025) (E.orient mixed035) (E.orient mixed235)
      h0 h1 h2 h3 h4 h5 (hE frame0235)
  change seed5ExtraRuleSame (E.orient mixed023) (E.orient mixed025) (E.orient mixed035) (E.orient mixed235)
  simpa [seed5ExtraMixedRule] using hrule

/-- Exact local XOR rule on the mixed six-packet 0345. -/
private theorem mixedRule0345
    (E : Hyper 5 (Fin 8))
    (hE : Admissible ({0,1,3} : Set ℕ) E)
    (hL : Preserves seed5ExtraLeft E (leftJointInclusion 6))
    (hR : Preserves seed5ExtraRight E (rightJointInclusion 6)) :
    seed5ExtraRuleSame ((seed5ExtraMixedBits E) 7) ((seed5ExtraMixedBits E) 8) ((seed5ExtraMixedBits E) 9) ((seed5ExtraMixedBits E) 19) := by
  have h0 : E.orient (facet frame0345 0) = false := by
    calc
      E.orient (facet frame0345 0) =
          E.orient (right0345.trans (rightJointInclusion 6)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5ExtraRight.orient right0345 := hR right0345
      _ = false := by
        have hm : StrictMono (right0345 : Fin 5 → Fin 7) := by decide
        change (Hyper.fromOrderedSigns seed5ExtraRightSigns).orient right0345 = false
        rw [fromOrderedSigns_orient_strictMono seed5ExtraRightSigns right0345 hm]
        decide
  have h5 : E.orient (facet frame0345 5) = false := by
    calc
      E.orient (facet frame0345 5) =
          E.orient (left0345.trans (leftJointInclusion 6)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5ExtraLeft.orient left0345 := hL left0345
      _ = false := by
        calc
          seed5ExtraLeft.orient left0345 =
              seed5ExtraLeftSigns (tupleVertices right0345) :=
            seed5Extra_left_rotated left0345 right0345
              (by ext i; fin_cases i <;> decide) (by decide)
          _ = false := by decide
  have h1 : E.orient (facet frame0345 1) = E.orient mixed345 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h2 : E.orient (facet frame0345 2) = E.orient mixed045 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h3 : E.orient (facet frame0345 3) = E.orient mixed035 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h4 : E.orient (facet frame0345 4) = E.orient mixed034 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have hrule : seed5ExtraMixedRule false false
      (E.orient mixed034) (E.orient mixed035) (E.orient mixed045) (E.orient mixed345) :=
    seed5ExtraMixedRule_of_admissible E frame0345 false false
      (E.orient mixed034) (E.orient mixed035) (E.orient mixed045) (E.orient mixed345)
      h0 h1 h2 h3 h4 h5 (hE frame0345)
  change seed5ExtraRuleSame (E.orient mixed034) (E.orient mixed035) (E.orient mixed045) (E.orient mixed345)
  simpa [seed5ExtraMixedRule] using hrule

/-- Exact local XOR rule on the mixed six-packet 1235. -/
private theorem mixedRule1235
    (E : Hyper 5 (Fin 8))
    (hE : Admissible ({0,1,3} : Set ℕ) E)
    (hL : Preserves seed5ExtraLeft E (leftJointInclusion 6))
    (hR : Preserves seed5ExtraRight E (rightJointInclusion 6)) :
    seed5ExtraRuleSame ((seed5ExtraMixedBits E) 10) ((seed5ExtraMixedBits E) 12) ((seed5ExtraMixedBits E) 14) ((seed5ExtraMixedBits E) 17) := by
  have h0 : E.orient (facet frame1235 0) = false := by
    calc
      E.orient (facet frame1235 0) =
          E.orient (right1235.trans (rightJointInclusion 6)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5ExtraRight.orient right1235 := hR right1235
      _ = false := by
        have hm : StrictMono (right1235 : Fin 5 → Fin 7) := by decide
        change (Hyper.fromOrderedSigns seed5ExtraRightSigns).orient right1235 = false
        rw [fromOrderedSigns_orient_strictMono seed5ExtraRightSigns right1235 hm]
        decide
  have h5 : E.orient (facet frame1235 5) = false := by
    calc
      E.orient (facet frame1235 5) =
          E.orient (left1235.trans (leftJointInclusion 6)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5ExtraLeft.orient left1235 := hL left1235
      _ = false := by
        calc
          seed5ExtraLeft.orient left1235 =
              seed5ExtraLeftSigns (tupleVertices right1235) :=
            seed5Extra_left_rotated left1235 right1235
              (by ext i; fin_cases i <;> decide) (by decide)
          _ = false := by decide
  have h1 : E.orient (facet frame1235 1) = E.orient mixed235 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h2 : E.orient (facet frame1235 2) = E.orient mixed135 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h3 : E.orient (facet frame1235 3) = E.orient mixed125 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h4 : E.orient (facet frame1235 4) = E.orient mixed123 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have hrule : seed5ExtraMixedRule false false
      (E.orient mixed123) (E.orient mixed125) (E.orient mixed135) (E.orient mixed235) :=
    seed5ExtraMixedRule_of_admissible E frame1235 false false
      (E.orient mixed123) (E.orient mixed125) (E.orient mixed135) (E.orient mixed235)
      h0 h1 h2 h3 h4 h5 (hE frame1235)
  change seed5ExtraRuleSame (E.orient mixed123) (E.orient mixed125) (E.orient mixed135) (E.orient mixed235)
  simpa [seed5ExtraMixedRule] using hrule

/-- Exact local XOR rule on the mixed six-packet 1345. -/
private theorem mixedRule1345
    (E : Hyper 5 (Fin 8))
    (hE : Admissible ({0,1,3} : Set ℕ) E)
    (hL : Preserves seed5ExtraLeft E (leftJointInclusion 6))
    (hR : Preserves seed5ExtraRight E (rightJointInclusion 6)) :
    seed5ExtraRuleSame ((seed5ExtraMixedBits E) 13) ((seed5ExtraMixedBits E) 14) ((seed5ExtraMixedBits E) 15) ((seed5ExtraMixedBits E) 19) := by
  have h0 : E.orient (facet frame1345 0) = false := by
    calc
      E.orient (facet frame1345 0) =
          E.orient (right1345.trans (rightJointInclusion 6)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5ExtraRight.orient right1345 := hR right1345
      _ = false := by
        have hm : StrictMono (right1345 : Fin 5 → Fin 7) := by decide
        change (Hyper.fromOrderedSigns seed5ExtraRightSigns).orient right1345 = false
        rw [fromOrderedSigns_orient_strictMono seed5ExtraRightSigns right1345 hm]
        decide
  have h5 : E.orient (facet frame1345 5) = false := by
    calc
      E.orient (facet frame1345 5) =
          E.orient (left1345.trans (leftJointInclusion 6)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5ExtraLeft.orient left1345 := hL left1345
      _ = false := by
        calc
          seed5ExtraLeft.orient left1345 =
              seed5ExtraLeftSigns (tupleVertices right1345) :=
            seed5Extra_left_rotated left1345 right1345
              (by ext i; fin_cases i <;> decide) (by decide)
          _ = false := by decide
  have h1 : E.orient (facet frame1345 1) = E.orient mixed345 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h2 : E.orient (facet frame1345 2) = E.orient mixed145 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h3 : E.orient (facet frame1345 3) = E.orient mixed135 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h4 : E.orient (facet frame1345 4) = E.orient mixed134 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have hrule : seed5ExtraMixedRule false false
      (E.orient mixed134) (E.orient mixed135) (E.orient mixed145) (E.orient mixed345) :=
    seed5ExtraMixedRule_of_admissible E frame1345 false false
      (E.orient mixed134) (E.orient mixed135) (E.orient mixed145) (E.orient mixed345)
      h0 h1 h2 h3 h4 h5 (hE frame1345)
  change seed5ExtraRuleSame (E.orient mixed134) (E.orient mixed135) (E.orient mixed145) (E.orient mixed345)
  simpa [seed5ExtraMixedRule] using hrule

/-- The nine actual packet constraints force the certified
twenty-variable XOR contradiction. -/
theorem seed5Extra_no_joint
    (E : Hyper 5 (Fin 8))
    (hE : Admissible ({0,1,3} : Set ℕ) E)
    (hL : Preserves seed5ExtraLeft E (leftJointInclusion 6))
    (hR : Preserves seed5ExtraRight E (rightJointInclusion 6)) :
    False := by
  exact seed5Extra_mixed_boolean_unsat (seed5ExtraMixedBits E)
    (mixedRule0123 E hE hL hR)
    (mixedRule0125 E hE hL hR)
    (mixedRule0134 E hE hL hR)
    (mixedRule0135 E hE hL hR)
    (mixedRule0145 E hE hL hR)
    (mixedRule0235 E hE hL hR)
    (mixedRule0345 E hE hL hR)
    (mixedRule1235 E hE hL hR)
    (mixedRule1345 E hE hL hR)

/-- Source links disagree at the increasing five-tuple [0,2,3,4,6].
Ordinary amalgamation cannot identify their new points. -/
theorem seed5Extra_disagreement :
    ∃ t : Fin 5 ↪ Fin 7,
      seed5ExtraLeft.orient t ≠ seed5ExtraRight.orient t := by
  let t : Fin 5 ↪ Fin 7 := ⟨![0,2,3,4,6], by decide⟩
  refine ⟨t, ?_⟩
  have hm : StrictMono (t : Fin 5 → Fin 7) := by decide
  change (Hyper.fromOrderedSigns seed5ExtraLeftSigns).orient t ≠
    (Hyper.fromOrderedSigns seed5ExtraRightSigns).orient t
  rw [fromOrderedSigns_orient_strictMono seed5ExtraLeftSigns t hm,
      fromOrderedSigns_orient_strictMono seed5ExtraRightSigns t hm]
  decide

/-- The 1 mod 4 exceptional arity-five class with allowed indices
{0,1,3} fails ordinary AP. -/
theorem seed5Extra_not_hasAP :
    ¬ HasAP 5 ({0,1,3} : Set ℕ) := by
  apply not_hasAP_of_no_joint
    seed5ExtraBase seed5ExtraLeft seed5ExtraRight
    seed5Extra_base_admissible seed5Extra_left_admissible
    seed5Extra_right_admissible seed5Extra_base_left seed5Extra_base_right
    seed5Extra_disagreement
  intro E hE hL hR
  exact seed5Extra_no_joint E hE hL hR

end Hypertournaments
