import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FinCases
import Hypertournaments.SeedFiveTwoPacketBridge

/-!
# Actual ordinary AP obstruction for the {0,3} arity-five class

The previously certified side tables and Boolean UNSAT core are now
connected through twenty literal mixed six-packets. All embeddings
are intrinsic and ordinary: identification of the two new points is
excluded by a separate explicit orientation disagreement.

The twenty packet lemmas below share the same proof architecture:
first and last facets come from the two side maps; the four middle
facets are the mixed x_{ijk} variables. The generic
seed5TwoMixedRule_of_admissible handles the normalized packet.
-/

namespace Hypertournaments

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-!
The left source link is presented with its new vertex at the end.
Moving it to the front crosses four coordinates, an even permutation.
We use this fixed rotation instead of evaluating the tuple sorter.
-/
private def frontShift5 : Equiv.Perm (Fin 5) :=
  (Equiv.swap (3 : Fin 5) 4) *
    (Equiv.swap (2 : Fin 5) 3) *
    (Equiv.swap (1 : Fin 5) 2) *
    (Equiv.swap (0 : Fin 5) 1)

private theorem frontShift5_even :
    frontShift5.sign = (1 : ℤˣ) := by
  have h34 : (Equiv.swap (3 : Fin 5) 4).sign = (-1 : ℤˣ) :=
    Equiv.Perm.sign_swap (by decide)
  have h23 : (Equiv.swap (2 : Fin 5) 3).sign = (-1 : ℤˣ) :=
    Equiv.Perm.sign_swap (by decide)
  have h12 : (Equiv.swap (1 : Fin 5) 2).sign = (-1 : ℤˣ) :=
    Equiv.Perm.sign_swap (by decide)
  have h01 : (Equiv.swap (0 : Fin 5) 1).sign = (-1 : ℤˣ) :=
    Equiv.Perm.sign_swap (by decide)
  simp [frontShift5, Equiv.Perm.sign_mul, h34, h23, h12, h01]

private theorem seed5Two_left_rotated
    (l rr : Fin 5 ↪ Fin 8)
    (hmatch : frontShift5.toEmbedding.trans rr = l)
    (hrmono : StrictMono (rr : Fin 5 → Fin 8)) :
    seed5TwoLeft.orient l = seed5TwoLeftSigns (tupleVertices rr) := by
  have hp : seed5TwoLeft.orient (frontShift5.toEmbedding.trans rr) =
      seed5TwoLeft.orient rr := by
    rw [Hyper.orient_perm]
    simp [frontShift5_even]
  calc
    seed5TwoLeft.orient l =
        seed5TwoLeft.orient (frontShift5.toEmbedding.trans rr) :=
      congrArg seed5TwoLeft.orient hmatch.symm
    _ = seed5TwoLeft.orient rr := hp
    _ = seed5TwoLeftSigns (tupleVertices rr) :=
      fromOrderedSigns_orient_strictMono seed5TwoLeftSigns rr hrmono

private def mixed012 : Fin 5 ↪ Fin 9 := ⟨![7,0,1,2,8], by decide⟩
private def mixed013 : Fin 5 ↪ Fin 9 := ⟨![7,0,1,3,8], by decide⟩
private def mixed014 : Fin 5 ↪ Fin 9 := ⟨![7,0,1,4,8], by decide⟩
private def mixed015 : Fin 5 ↪ Fin 9 := ⟨![7,0,1,5,8], by decide⟩
private def mixed016 : Fin 5 ↪ Fin 9 := ⟨![7,0,1,6,8], by decide⟩
private def mixed023 : Fin 5 ↪ Fin 9 := ⟨![7,0,2,3,8], by decide⟩
private def mixed024 : Fin 5 ↪ Fin 9 := ⟨![7,0,2,4,8], by decide⟩
private def mixed025 : Fin 5 ↪ Fin 9 := ⟨![7,0,2,5,8], by decide⟩
private def mixed026 : Fin 5 ↪ Fin 9 := ⟨![7,0,2,6,8], by decide⟩
private def mixed034 : Fin 5 ↪ Fin 9 := ⟨![7,0,3,4,8], by decide⟩
private def mixed035 : Fin 5 ↪ Fin 9 := ⟨![7,0,3,5,8], by decide⟩
private def mixed036 : Fin 5 ↪ Fin 9 := ⟨![7,0,3,6,8], by decide⟩
private def mixed045 : Fin 5 ↪ Fin 9 := ⟨![7,0,4,5,8], by decide⟩
private def mixed046 : Fin 5 ↪ Fin 9 := ⟨![7,0,4,6,8], by decide⟩
private def mixed056 : Fin 5 ↪ Fin 9 := ⟨![7,0,5,6,8], by decide⟩
private def mixed123 : Fin 5 ↪ Fin 9 := ⟨![7,1,2,3,8], by decide⟩
private def mixed124 : Fin 5 ↪ Fin 9 := ⟨![7,1,2,4,8], by decide⟩
private def mixed125 : Fin 5 ↪ Fin 9 := ⟨![7,1,2,5,8], by decide⟩
private def mixed126 : Fin 5 ↪ Fin 9 := ⟨![7,1,2,6,8], by decide⟩
private def mixed134 : Fin 5 ↪ Fin 9 := ⟨![7,1,3,4,8], by decide⟩
private def mixed135 : Fin 5 ↪ Fin 9 := ⟨![7,1,3,5,8], by decide⟩
private def mixed136 : Fin 5 ↪ Fin 9 := ⟨![7,1,3,6,8], by decide⟩
private def mixed145 : Fin 5 ↪ Fin 9 := ⟨![7,1,4,5,8], by decide⟩
private def mixed146 : Fin 5 ↪ Fin 9 := ⟨![7,1,4,6,8], by decide⟩
private def mixed156 : Fin 5 ↪ Fin 9 := ⟨![7,1,5,6,8], by decide⟩
private def mixed234 : Fin 5 ↪ Fin 9 := ⟨![7,2,3,4,8], by decide⟩
private def mixed235 : Fin 5 ↪ Fin 9 := ⟨![7,2,3,5,8], by decide⟩
private def mixed236 : Fin 5 ↪ Fin 9 := ⟨![7,2,3,6,8], by decide⟩
private def mixed245 : Fin 5 ↪ Fin 9 := ⟨![7,2,4,5,8], by decide⟩
private def mixed246 : Fin 5 ↪ Fin 9 := ⟨![7,2,4,6,8], by decide⟩
private def mixed256 : Fin 5 ↪ Fin 9 := ⟨![7,2,5,6,8], by decide⟩
private def mixed345 : Fin 5 ↪ Fin 9 := ⟨![7,3,4,5,8], by decide⟩
private def mixed346 : Fin 5 ↪ Fin 9 := ⟨![7,3,4,6,8], by decide⟩
private def mixed356 : Fin 5 ↪ Fin 9 := ⟨![7,3,5,6,8], by decide⟩
private def mixed456 : Fin 5 ↪ Fin 9 := ⟨![7,4,5,6,8], by decide⟩

/-- All thirty-five mixed five-set orientations in lexicographic triple order. -/
def seed5TwoMixedBits (E : Hyper 5 (Fin 9)) : Fin 35 → Bool :=
  ![E.orient mixed012,
    E.orient mixed013,
    E.orient mixed014,
    E.orient mixed015,
    E.orient mixed016,
    E.orient mixed023,
    E.orient mixed024,
    E.orient mixed025,
    E.orient mixed026,
    E.orient mixed034,
    E.orient mixed035,
    E.orient mixed036,
    E.orient mixed045,
    E.orient mixed046,
    E.orient mixed056,
    E.orient mixed123,
    E.orient mixed124,
    E.orient mixed125,
    E.orient mixed126,
    E.orient mixed134,
    E.orient mixed135,
    E.orient mixed136,
    E.orient mixed145,
    E.orient mixed146,
    E.orient mixed156,
    E.orient mixed234,
    E.orient mixed235,
    E.orient mixed236,
    E.orient mixed245,
    E.orient mixed246,
    E.orient mixed256,
    E.orient mixed345,
    E.orient mixed346,
    E.orient mixed356,
    E.orient mixed456]

private def frame0125 : Fin 6 ↪ Fin 9 := ⟨![7,0,1,2,5,8], by decide⟩
private def left0125 : Fin 5 ↪ Fin 8 := ⟨![7,0,1,2,5], by decide⟩
private def right0125 : Fin 5 ↪ Fin 8 := ⟨![0,1,2,5,7], by decide⟩
private def frame0134 : Fin 6 ↪ Fin 9 := ⟨![7,0,1,3,4,8], by decide⟩
private def left0134 : Fin 5 ↪ Fin 8 := ⟨![7,0,1,3,4], by decide⟩
private def right0134 : Fin 5 ↪ Fin 8 := ⟨![0,1,3,4,7], by decide⟩
private def frame0136 : Fin 6 ↪ Fin 9 := ⟨![7,0,1,3,6,8], by decide⟩
private def left0136 : Fin 5 ↪ Fin 8 := ⟨![7,0,1,3,6], by decide⟩
private def right0136 : Fin 5 ↪ Fin 8 := ⟨![0,1,3,6,7], by decide⟩
private def frame0156 : Fin 6 ↪ Fin 9 := ⟨![7,0,1,5,6,8], by decide⟩
private def left0156 : Fin 5 ↪ Fin 8 := ⟨![7,0,1,5,6], by decide⟩
private def right0156 : Fin 5 ↪ Fin 8 := ⟨![0,1,5,6,7], by decide⟩
private def frame0235 : Fin 6 ↪ Fin 9 := ⟨![7,0,2,3,5,8], by decide⟩
private def left0235 : Fin 5 ↪ Fin 8 := ⟨![7,0,2,3,5], by decide⟩
private def right0235 : Fin 5 ↪ Fin 8 := ⟨![0,2,3,5,7], by decide⟩
private def frame0236 : Fin 6 ↪ Fin 9 := ⟨![7,0,2,3,6,8], by decide⟩
private def left0236 : Fin 5 ↪ Fin 8 := ⟨![7,0,2,3,6], by decide⟩
private def right0236 : Fin 5 ↪ Fin 8 := ⟨![0,2,3,6,7], by decide⟩
private def frame0246 : Fin 6 ↪ Fin 9 := ⟨![7,0,2,4,6,8], by decide⟩
private def left0246 : Fin 5 ↪ Fin 8 := ⟨![7,0,2,4,6], by decide⟩
private def right0246 : Fin 5 ↪ Fin 8 := ⟨![0,2,4,6,7], by decide⟩
private def frame0256 : Fin 6 ↪ Fin 9 := ⟨![7,0,2,5,6,8], by decide⟩
private def left0256 : Fin 5 ↪ Fin 8 := ⟨![7,0,2,5,6], by decide⟩
private def right0256 : Fin 5 ↪ Fin 8 := ⟨![0,2,5,6,7], by decide⟩
private def frame0345 : Fin 6 ↪ Fin 9 := ⟨![7,0,3,4,5,8], by decide⟩
private def left0345 : Fin 5 ↪ Fin 8 := ⟨![7,0,3,4,5], by decide⟩
private def right0345 : Fin 5 ↪ Fin 8 := ⟨![0,3,4,5,7], by decide⟩
private def frame0356 : Fin 6 ↪ Fin 9 := ⟨![7,0,3,5,6,8], by decide⟩
private def left0356 : Fin 5 ↪ Fin 8 := ⟨![7,0,3,5,6], by decide⟩
private def right0356 : Fin 5 ↪ Fin 8 := ⟨![0,3,5,6,7], by decide⟩
private def frame0456 : Fin 6 ↪ Fin 9 := ⟨![7,0,4,5,6,8], by decide⟩
private def left0456 : Fin 5 ↪ Fin 8 := ⟨![7,0,4,5,6], by decide⟩
private def right0456 : Fin 5 ↪ Fin 8 := ⟨![0,4,5,6,7], by decide⟩
private def frame1236 : Fin 6 ↪ Fin 9 := ⟨![7,1,2,3,6,8], by decide⟩
private def left1236 : Fin 5 ↪ Fin 8 := ⟨![7,1,2,3,6], by decide⟩
private def right1236 : Fin 5 ↪ Fin 8 := ⟨![1,2,3,6,7], by decide⟩
private def frame1246 : Fin 6 ↪ Fin 9 := ⟨![7,1,2,4,6,8], by decide⟩
private def left1246 : Fin 5 ↪ Fin 8 := ⟨![7,1,2,4,6], by decide⟩
private def right1246 : Fin 5 ↪ Fin 8 := ⟨![1,2,4,6,7], by decide⟩
private def frame1256 : Fin 6 ↪ Fin 9 := ⟨![7,1,2,5,6,8], by decide⟩
private def left1256 : Fin 5 ↪ Fin 8 := ⟨![7,1,2,5,6], by decide⟩
private def right1256 : Fin 5 ↪ Fin 8 := ⟨![1,2,5,6,7], by decide⟩
private def frame1345 : Fin 6 ↪ Fin 9 := ⟨![7,1,3,4,5,8], by decide⟩
private def left1345 : Fin 5 ↪ Fin 8 := ⟨![7,1,3,4,5], by decide⟩
private def right1345 : Fin 5 ↪ Fin 8 := ⟨![1,3,4,5,7], by decide⟩
private def frame1356 : Fin 6 ↪ Fin 9 := ⟨![7,1,3,5,6,8], by decide⟩
private def left1356 : Fin 5 ↪ Fin 8 := ⟨![7,1,3,5,6], by decide⟩
private def right1356 : Fin 5 ↪ Fin 8 := ⟨![1,3,5,6,7], by decide⟩
private def frame1456 : Fin 6 ↪ Fin 9 := ⟨![7,1,4,5,6,8], by decide⟩
private def left1456 : Fin 5 ↪ Fin 8 := ⟨![7,1,4,5,6], by decide⟩
private def right1456 : Fin 5 ↪ Fin 8 := ⟨![1,4,5,6,7], by decide⟩
private def frame2345 : Fin 6 ↪ Fin 9 := ⟨![7,2,3,4,5,8], by decide⟩
private def left2345 : Fin 5 ↪ Fin 8 := ⟨![7,2,3,4,5], by decide⟩
private def right2345 : Fin 5 ↪ Fin 8 := ⟨![2,3,4,5,7], by decide⟩
private def frame2346 : Fin 6 ↪ Fin 9 := ⟨![7,2,3,4,6,8], by decide⟩
private def left2346 : Fin 5 ↪ Fin 8 := ⟨![7,2,3,4,6], by decide⟩
private def right2346 : Fin 5 ↪ Fin 8 := ⟨![2,3,4,6,7], by decide⟩
private def frame2456 : Fin 6 ↪ Fin 9 := ⟨![7,2,4,5,6,8], by decide⟩
private def left2456 : Fin 5 ↪ Fin 8 := ⟨![7,2,4,5,6], by decide⟩
private def right2456 : Fin 5 ↪ Fin 8 := ⟨![2,4,5,6,7], by decide⟩

/-- Mixed packet 0125 satisfies its exact permitted six-facet Boolean rule. -/
private theorem mixedRule0125
    (E : Hyper 5 (Fin 9))
    (hE : Admissible ({0,3} : Set ℕ) E)
    (hL : Preserves seed5TwoLeft E (leftJointInclusion 7))
    (hR : Preserves seed5TwoRight E (rightJointInclusion 7)) :
    seed5TwoRuleZeroOne ((seed5TwoMixedBits E) 0) ((seed5TwoMixedBits E) 3) ((seed5TwoMixedBits E) 7) ((seed5TwoMixedBits E) 17) := by
  have h0 : E.orient (facet frame0125 0) = false := by
    calc
      E.orient (facet frame0125 0) =
          E.orient (right0125.trans (rightJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoRight.orient right0125 := hR right0125
      _ = false := by
        have hm : StrictMono (right0125 : Fin 5 → Fin 8) := by decide
        change (Hyper.fromOrderedSigns seed5TwoRightSigns).orient right0125 = false
        rw [fromOrderedSigns_orient_strictMono seed5TwoRightSigns right0125 hm]
        decide
  have h5 : E.orient (facet frame0125 5) = true := by
    calc
      E.orient (facet frame0125 5) =
          E.orient (left0125.trans (leftJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoLeft.orient left0125 := hL left0125
      _ = true := by
        calc
          seed5TwoLeft.orient left0125 =
              seed5TwoLeftSigns (tupleVertices right0125) :=
            seed5Two_left_rotated left0125 right0125
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
  have hrule : seed5TwoMixedRule false true
      (E.orient mixed012) (E.orient mixed015) (E.orient mixed025) (E.orient mixed125) :=
    seed5TwoMixedRule_of_admissible E frame0125 false true
      (E.orient mixed012) (E.orient mixed015) (E.orient mixed025) (E.orient mixed125)
      h0 h1 h2 h3 h4 h5 (hE frame0125)
  change seed5TwoRuleZeroOne (E.orient mixed012) (E.orient mixed015) (E.orient mixed025) (E.orient mixed125)
  simpa [seed5TwoMixedRule] using hrule

/-- Mixed packet 0134 satisfies its exact permitted six-facet Boolean rule. -/
private theorem mixedRule0134
    (E : Hyper 5 (Fin 9))
    (hE : Admissible ({0,3} : Set ℕ) E)
    (hL : Preserves seed5TwoLeft E (leftJointInclusion 7))
    (hR : Preserves seed5TwoRight E (rightJointInclusion 7)) :
    seed5TwoRuleOneZero ((seed5TwoMixedBits E) 1) ((seed5TwoMixedBits E) 2) ((seed5TwoMixedBits E) 9) ((seed5TwoMixedBits E) 19) := by
  have h0 : E.orient (facet frame0134 0) = true := by
    calc
      E.orient (facet frame0134 0) =
          E.orient (right0134.trans (rightJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoRight.orient right0134 := hR right0134
      _ = true := by
        have hm : StrictMono (right0134 : Fin 5 → Fin 8) := by decide
        change (Hyper.fromOrderedSigns seed5TwoRightSigns).orient right0134 = true
        rw [fromOrderedSigns_orient_strictMono seed5TwoRightSigns right0134 hm]
        decide
  have h5 : E.orient (facet frame0134 5) = false := by
    calc
      E.orient (facet frame0134 5) =
          E.orient (left0134.trans (leftJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoLeft.orient left0134 := hL left0134
      _ = false := by
        calc
          seed5TwoLeft.orient left0134 =
              seed5TwoLeftSigns (tupleVertices right0134) :=
            seed5Two_left_rotated left0134 right0134
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
  have hrule : seed5TwoMixedRule true false
      (E.orient mixed013) (E.orient mixed014) (E.orient mixed034) (E.orient mixed134) :=
    seed5TwoMixedRule_of_admissible E frame0134 true false
      (E.orient mixed013) (E.orient mixed014) (E.orient mixed034) (E.orient mixed134)
      h0 h1 h2 h3 h4 h5 (hE frame0134)
  change seed5TwoRuleOneZero (E.orient mixed013) (E.orient mixed014) (E.orient mixed034) (E.orient mixed134)
  simpa [seed5TwoMixedRule] using hrule

/-- Mixed packet 0136 satisfies its exact permitted six-facet Boolean rule. -/
private theorem mixedRule0136
    (E : Hyper 5 (Fin 9))
    (hE : Admissible ({0,3} : Set ℕ) E)
    (hL : Preserves seed5TwoLeft E (leftJointInclusion 7))
    (hR : Preserves seed5TwoRight E (rightJointInclusion 7)) :
    seed5TwoRuleSame ((seed5TwoMixedBits E) 1) ((seed5TwoMixedBits E) 4) ((seed5TwoMixedBits E) 11) ((seed5TwoMixedBits E) 21) := by
  have h0 : E.orient (facet frame0136 0) = false := by
    calc
      E.orient (facet frame0136 0) =
          E.orient (right0136.trans (rightJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoRight.orient right0136 := hR right0136
      _ = false := by
        have hm : StrictMono (right0136 : Fin 5 → Fin 8) := by decide
        change (Hyper.fromOrderedSigns seed5TwoRightSigns).orient right0136 = false
        rw [fromOrderedSigns_orient_strictMono seed5TwoRightSigns right0136 hm]
        decide
  have h5 : E.orient (facet frame0136 5) = false := by
    calc
      E.orient (facet frame0136 5) =
          E.orient (left0136.trans (leftJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoLeft.orient left0136 := hL left0136
      _ = false := by
        calc
          seed5TwoLeft.orient left0136 =
              seed5TwoLeftSigns (tupleVertices right0136) :=
            seed5Two_left_rotated left0136 right0136
              (by ext i; fin_cases i <;> decide) (by decide)
          _ = false := by decide
  have h1 : E.orient (facet frame0136 1) = E.orient mixed136 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h2 : E.orient (facet frame0136 2) = E.orient mixed036 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h3 : E.orient (facet frame0136 3) = E.orient mixed016 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h4 : E.orient (facet frame0136 4) = E.orient mixed013 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have hrule : seed5TwoMixedRule false false
      (E.orient mixed013) (E.orient mixed016) (E.orient mixed036) (E.orient mixed136) :=
    seed5TwoMixedRule_of_admissible E frame0136 false false
      (E.orient mixed013) (E.orient mixed016) (E.orient mixed036) (E.orient mixed136)
      h0 h1 h2 h3 h4 h5 (hE frame0136)
  change seed5TwoRuleSame (E.orient mixed013) (E.orient mixed016) (E.orient mixed036) (E.orient mixed136)
  simpa [seed5TwoMixedRule] using hrule

/-- Mixed packet 0156 satisfies its exact permitted six-facet Boolean rule. -/
private theorem mixedRule0156
    (E : Hyper 5 (Fin 9))
    (hE : Admissible ({0,3} : Set ℕ) E)
    (hL : Preserves seed5TwoLeft E (leftJointInclusion 7))
    (hR : Preserves seed5TwoRight E (rightJointInclusion 7)) :
    seed5TwoRuleOneZero ((seed5TwoMixedBits E) 3) ((seed5TwoMixedBits E) 4) ((seed5TwoMixedBits E) 14) ((seed5TwoMixedBits E) 24) := by
  have h0 : E.orient (facet frame0156 0) = true := by
    calc
      E.orient (facet frame0156 0) =
          E.orient (right0156.trans (rightJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoRight.orient right0156 := hR right0156
      _ = true := by
        have hm : StrictMono (right0156 : Fin 5 → Fin 8) := by decide
        change (Hyper.fromOrderedSigns seed5TwoRightSigns).orient right0156 = true
        rw [fromOrderedSigns_orient_strictMono seed5TwoRightSigns right0156 hm]
        decide
  have h5 : E.orient (facet frame0156 5) = false := by
    calc
      E.orient (facet frame0156 5) =
          E.orient (left0156.trans (leftJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoLeft.orient left0156 := hL left0156
      _ = false := by
        calc
          seed5TwoLeft.orient left0156 =
              seed5TwoLeftSigns (tupleVertices right0156) :=
            seed5Two_left_rotated left0156 right0156
              (by ext i; fin_cases i <;> decide) (by decide)
          _ = false := by decide
  have h1 : E.orient (facet frame0156 1) = E.orient mixed156 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h2 : E.orient (facet frame0156 2) = E.orient mixed056 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h3 : E.orient (facet frame0156 3) = E.orient mixed016 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h4 : E.orient (facet frame0156 4) = E.orient mixed015 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have hrule : seed5TwoMixedRule true false
      (E.orient mixed015) (E.orient mixed016) (E.orient mixed056) (E.orient mixed156) :=
    seed5TwoMixedRule_of_admissible E frame0156 true false
      (E.orient mixed015) (E.orient mixed016) (E.orient mixed056) (E.orient mixed156)
      h0 h1 h2 h3 h4 h5 (hE frame0156)
  change seed5TwoRuleOneZero (E.orient mixed015) (E.orient mixed016) (E.orient mixed056) (E.orient mixed156)
  simpa [seed5TwoMixedRule] using hrule

/-- Mixed packet 0235 satisfies its exact permitted six-facet Boolean rule. -/
private theorem mixedRule0235
    (E : Hyper 5 (Fin 9))
    (hE : Admissible ({0,3} : Set ℕ) E)
    (hL : Preserves seed5TwoLeft E (leftJointInclusion 7))
    (hR : Preserves seed5TwoRight E (rightJointInclusion 7)) :
    seed5TwoRuleSame ((seed5TwoMixedBits E) 5) ((seed5TwoMixedBits E) 7) ((seed5TwoMixedBits E) 10) ((seed5TwoMixedBits E) 26) := by
  have h0 : E.orient (facet frame0235 0) = false := by
    calc
      E.orient (facet frame0235 0) =
          E.orient (right0235.trans (rightJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoRight.orient right0235 := hR right0235
      _ = false := by
        have hm : StrictMono (right0235 : Fin 5 → Fin 8) := by decide
        change (Hyper.fromOrderedSigns seed5TwoRightSigns).orient right0235 = false
        rw [fromOrderedSigns_orient_strictMono seed5TwoRightSigns right0235 hm]
        decide
  have h5 : E.orient (facet frame0235 5) = false := by
    calc
      E.orient (facet frame0235 5) =
          E.orient (left0235.trans (leftJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoLeft.orient left0235 := hL left0235
      _ = false := by
        calc
          seed5TwoLeft.orient left0235 =
              seed5TwoLeftSigns (tupleVertices right0235) :=
            seed5Two_left_rotated left0235 right0235
              (by ext i; fin_cases i <;> decide) (by decide)
          _ = false := by decide
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
  have hrule : seed5TwoMixedRule false false
      (E.orient mixed023) (E.orient mixed025) (E.orient mixed035) (E.orient mixed235) :=
    seed5TwoMixedRule_of_admissible E frame0235 false false
      (E.orient mixed023) (E.orient mixed025) (E.orient mixed035) (E.orient mixed235)
      h0 h1 h2 h3 h4 h5 (hE frame0235)
  change seed5TwoRuleSame (E.orient mixed023) (E.orient mixed025) (E.orient mixed035) (E.orient mixed235)
  simpa [seed5TwoMixedRule] using hrule

/-- Mixed packet 0236 satisfies its exact permitted six-facet Boolean rule. -/
private theorem mixedRule0236
    (E : Hyper 5 (Fin 9))
    (hE : Admissible ({0,3} : Set ℕ) E)
    (hL : Preserves seed5TwoLeft E (leftJointInclusion 7))
    (hR : Preserves seed5TwoRight E (rightJointInclusion 7)) :
    seed5TwoRuleOneZero ((seed5TwoMixedBits E) 5) ((seed5TwoMixedBits E) 8) ((seed5TwoMixedBits E) 11) ((seed5TwoMixedBits E) 27) := by
  have h0 : E.orient (facet frame0236 0) = true := by
    calc
      E.orient (facet frame0236 0) =
          E.orient (right0236.trans (rightJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoRight.orient right0236 := hR right0236
      _ = true := by
        have hm : StrictMono (right0236 : Fin 5 → Fin 8) := by decide
        change (Hyper.fromOrderedSigns seed5TwoRightSigns).orient right0236 = true
        rw [fromOrderedSigns_orient_strictMono seed5TwoRightSigns right0236 hm]
        decide
  have h5 : E.orient (facet frame0236 5) = false := by
    calc
      E.orient (facet frame0236 5) =
          E.orient (left0236.trans (leftJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoLeft.orient left0236 := hL left0236
      _ = false := by
        calc
          seed5TwoLeft.orient left0236 =
              seed5TwoLeftSigns (tupleVertices right0236) :=
            seed5Two_left_rotated left0236 right0236
              (by ext i; fin_cases i <;> decide) (by decide)
          _ = false := by decide
  have h1 : E.orient (facet frame0236 1) = E.orient mixed236 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h2 : E.orient (facet frame0236 2) = E.orient mixed036 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h3 : E.orient (facet frame0236 3) = E.orient mixed026 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h4 : E.orient (facet frame0236 4) = E.orient mixed023 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have hrule : seed5TwoMixedRule true false
      (E.orient mixed023) (E.orient mixed026) (E.orient mixed036) (E.orient mixed236) :=
    seed5TwoMixedRule_of_admissible E frame0236 true false
      (E.orient mixed023) (E.orient mixed026) (E.orient mixed036) (E.orient mixed236)
      h0 h1 h2 h3 h4 h5 (hE frame0236)
  change seed5TwoRuleOneZero (E.orient mixed023) (E.orient mixed026) (E.orient mixed036) (E.orient mixed236)
  simpa [seed5TwoMixedRule] using hrule

/-- Mixed packet 0246 satisfies its exact permitted six-facet Boolean rule. -/
private theorem mixedRule0246
    (E : Hyper 5 (Fin 9))
    (hE : Admissible ({0,3} : Set ℕ) E)
    (hL : Preserves seed5TwoLeft E (leftJointInclusion 7))
    (hR : Preserves seed5TwoRight E (rightJointInclusion 7)) :
    seed5TwoRuleSame ((seed5TwoMixedBits E) 6) ((seed5TwoMixedBits E) 8) ((seed5TwoMixedBits E) 13) ((seed5TwoMixedBits E) 29) := by
  have h0 : E.orient (facet frame0246 0) = false := by
    calc
      E.orient (facet frame0246 0) =
          E.orient (right0246.trans (rightJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoRight.orient right0246 := hR right0246
      _ = false := by
        have hm : StrictMono (right0246 : Fin 5 → Fin 8) := by decide
        change (Hyper.fromOrderedSigns seed5TwoRightSigns).orient right0246 = false
        rw [fromOrderedSigns_orient_strictMono seed5TwoRightSigns right0246 hm]
        decide
  have h5 : E.orient (facet frame0246 5) = false := by
    calc
      E.orient (facet frame0246 5) =
          E.orient (left0246.trans (leftJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoLeft.orient left0246 := hL left0246
      _ = false := by
        calc
          seed5TwoLeft.orient left0246 =
              seed5TwoLeftSigns (tupleVertices right0246) :=
            seed5Two_left_rotated left0246 right0246
              (by ext i; fin_cases i <;> decide) (by decide)
          _ = false := by decide
  have h1 : E.orient (facet frame0246 1) = E.orient mixed246 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h2 : E.orient (facet frame0246 2) = E.orient mixed046 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h3 : E.orient (facet frame0246 3) = E.orient mixed026 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h4 : E.orient (facet frame0246 4) = E.orient mixed024 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have hrule : seed5TwoMixedRule false false
      (E.orient mixed024) (E.orient mixed026) (E.orient mixed046) (E.orient mixed246) :=
    seed5TwoMixedRule_of_admissible E frame0246 false false
      (E.orient mixed024) (E.orient mixed026) (E.orient mixed046) (E.orient mixed246)
      h0 h1 h2 h3 h4 h5 (hE frame0246)
  change seed5TwoRuleSame (E.orient mixed024) (E.orient mixed026) (E.orient mixed046) (E.orient mixed246)
  simpa [seed5TwoMixedRule] using hrule

/-- Mixed packet 0256 satisfies its exact permitted six-facet Boolean rule. -/
private theorem mixedRule0256
    (E : Hyper 5 (Fin 9))
    (hE : Admissible ({0,3} : Set ℕ) E)
    (hL : Preserves seed5TwoLeft E (leftJointInclusion 7))
    (hR : Preserves seed5TwoRight E (rightJointInclusion 7)) :
    seed5TwoRuleOneZero ((seed5TwoMixedBits E) 7) ((seed5TwoMixedBits E) 8) ((seed5TwoMixedBits E) 14) ((seed5TwoMixedBits E) 30) := by
  have h0 : E.orient (facet frame0256 0) = true := by
    calc
      E.orient (facet frame0256 0) =
          E.orient (right0256.trans (rightJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoRight.orient right0256 := hR right0256
      _ = true := by
        have hm : StrictMono (right0256 : Fin 5 → Fin 8) := by decide
        change (Hyper.fromOrderedSigns seed5TwoRightSigns).orient right0256 = true
        rw [fromOrderedSigns_orient_strictMono seed5TwoRightSigns right0256 hm]
        decide
  have h5 : E.orient (facet frame0256 5) = false := by
    calc
      E.orient (facet frame0256 5) =
          E.orient (left0256.trans (leftJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoLeft.orient left0256 := hL left0256
      _ = false := by
        calc
          seed5TwoLeft.orient left0256 =
              seed5TwoLeftSigns (tupleVertices right0256) :=
            seed5Two_left_rotated left0256 right0256
              (by ext i; fin_cases i <;> decide) (by decide)
          _ = false := by decide
  have h1 : E.orient (facet frame0256 1) = E.orient mixed256 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h2 : E.orient (facet frame0256 2) = E.orient mixed056 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h3 : E.orient (facet frame0256 3) = E.orient mixed026 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h4 : E.orient (facet frame0256 4) = E.orient mixed025 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have hrule : seed5TwoMixedRule true false
      (E.orient mixed025) (E.orient mixed026) (E.orient mixed056) (E.orient mixed256) :=
    seed5TwoMixedRule_of_admissible E frame0256 true false
      (E.orient mixed025) (E.orient mixed026) (E.orient mixed056) (E.orient mixed256)
      h0 h1 h2 h3 h4 h5 (hE frame0256)
  change seed5TwoRuleOneZero (E.orient mixed025) (E.orient mixed026) (E.orient mixed056) (E.orient mixed256)
  simpa [seed5TwoMixedRule] using hrule

/-- Mixed packet 0345 satisfies its exact permitted six-facet Boolean rule. -/
private theorem mixedRule0345
    (E : Hyper 5 (Fin 9))
    (hE : Admissible ({0,3} : Set ℕ) E)
    (hL : Preserves seed5TwoLeft E (leftJointInclusion 7))
    (hR : Preserves seed5TwoRight E (rightJointInclusion 7)) :
    seed5TwoRuleZeroOne ((seed5TwoMixedBits E) 9) ((seed5TwoMixedBits E) 10) ((seed5TwoMixedBits E) 12) ((seed5TwoMixedBits E) 31) := by
  have h0 : E.orient (facet frame0345 0) = false := by
    calc
      E.orient (facet frame0345 0) =
          E.orient (right0345.trans (rightJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoRight.orient right0345 := hR right0345
      _ = false := by
        have hm : StrictMono (right0345 : Fin 5 → Fin 8) := by decide
        change (Hyper.fromOrderedSigns seed5TwoRightSigns).orient right0345 = false
        rw [fromOrderedSigns_orient_strictMono seed5TwoRightSigns right0345 hm]
        decide
  have h5 : E.orient (facet frame0345 5) = true := by
    calc
      E.orient (facet frame0345 5) =
          E.orient (left0345.trans (leftJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoLeft.orient left0345 := hL left0345
      _ = true := by
        calc
          seed5TwoLeft.orient left0345 =
              seed5TwoLeftSigns (tupleVertices right0345) :=
            seed5Two_left_rotated left0345 right0345
              (by ext i; fin_cases i <;> decide) (by decide)
          _ = true := by decide
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
  have hrule : seed5TwoMixedRule false true
      (E.orient mixed034) (E.orient mixed035) (E.orient mixed045) (E.orient mixed345) :=
    seed5TwoMixedRule_of_admissible E frame0345 false true
      (E.orient mixed034) (E.orient mixed035) (E.orient mixed045) (E.orient mixed345)
      h0 h1 h2 h3 h4 h5 (hE frame0345)
  change seed5TwoRuleZeroOne (E.orient mixed034) (E.orient mixed035) (E.orient mixed045) (E.orient mixed345)
  simpa [seed5TwoMixedRule] using hrule

/-- Mixed packet 0356 satisfies its exact permitted six-facet Boolean rule. -/
private theorem mixedRule0356
    (E : Hyper 5 (Fin 9))
    (hE : Admissible ({0,3} : Set ℕ) E)
    (hL : Preserves seed5TwoLeft E (leftJointInclusion 7))
    (hR : Preserves seed5TwoRight E (rightJointInclusion 7)) :
    seed5TwoRuleOneZero ((seed5TwoMixedBits E) 10) ((seed5TwoMixedBits E) 11) ((seed5TwoMixedBits E) 14) ((seed5TwoMixedBits E) 33) := by
  have h0 : E.orient (facet frame0356 0) = true := by
    calc
      E.orient (facet frame0356 0) =
          E.orient (right0356.trans (rightJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoRight.orient right0356 := hR right0356
      _ = true := by
        have hm : StrictMono (right0356 : Fin 5 → Fin 8) := by decide
        change (Hyper.fromOrderedSigns seed5TwoRightSigns).orient right0356 = true
        rw [fromOrderedSigns_orient_strictMono seed5TwoRightSigns right0356 hm]
        decide
  have h5 : E.orient (facet frame0356 5) = false := by
    calc
      E.orient (facet frame0356 5) =
          E.orient (left0356.trans (leftJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoLeft.orient left0356 := hL left0356
      _ = false := by
        calc
          seed5TwoLeft.orient left0356 =
              seed5TwoLeftSigns (tupleVertices right0356) :=
            seed5Two_left_rotated left0356 right0356
              (by ext i; fin_cases i <;> decide) (by decide)
          _ = false := by decide
  have h1 : E.orient (facet frame0356 1) = E.orient mixed356 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h2 : E.orient (facet frame0356 2) = E.orient mixed056 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h3 : E.orient (facet frame0356 3) = E.orient mixed036 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h4 : E.orient (facet frame0356 4) = E.orient mixed035 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have hrule : seed5TwoMixedRule true false
      (E.orient mixed035) (E.orient mixed036) (E.orient mixed056) (E.orient mixed356) :=
    seed5TwoMixedRule_of_admissible E frame0356 true false
      (E.orient mixed035) (E.orient mixed036) (E.orient mixed056) (E.orient mixed356)
      h0 h1 h2 h3 h4 h5 (hE frame0356)
  change seed5TwoRuleOneZero (E.orient mixed035) (E.orient mixed036) (E.orient mixed056) (E.orient mixed356)
  simpa [seed5TwoMixedRule] using hrule

/-- Mixed packet 0456 satisfies its exact permitted six-facet Boolean rule. -/
private theorem mixedRule0456
    (E : Hyper 5 (Fin 9))
    (hE : Admissible ({0,3} : Set ℕ) E)
    (hL : Preserves seed5TwoLeft E (leftJointInclusion 7))
    (hR : Preserves seed5TwoRight E (rightJointInclusion 7)) :
    seed5TwoRuleSame ((seed5TwoMixedBits E) 12) ((seed5TwoMixedBits E) 13) ((seed5TwoMixedBits E) 14) ((seed5TwoMixedBits E) 34) := by
  have h0 : E.orient (facet frame0456 0) = false := by
    calc
      E.orient (facet frame0456 0) =
          E.orient (right0456.trans (rightJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoRight.orient right0456 := hR right0456
      _ = false := by
        have hm : StrictMono (right0456 : Fin 5 → Fin 8) := by decide
        change (Hyper.fromOrderedSigns seed5TwoRightSigns).orient right0456 = false
        rw [fromOrderedSigns_orient_strictMono seed5TwoRightSigns right0456 hm]
        decide
  have h5 : E.orient (facet frame0456 5) = false := by
    calc
      E.orient (facet frame0456 5) =
          E.orient (left0456.trans (leftJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoLeft.orient left0456 := hL left0456
      _ = false := by
        calc
          seed5TwoLeft.orient left0456 =
              seed5TwoLeftSigns (tupleVertices right0456) :=
            seed5Two_left_rotated left0456 right0456
              (by ext i; fin_cases i <;> decide) (by decide)
          _ = false := by decide
  have h1 : E.orient (facet frame0456 1) = E.orient mixed456 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h2 : E.orient (facet frame0456 2) = E.orient mixed056 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h3 : E.orient (facet frame0456 3) = E.orient mixed046 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h4 : E.orient (facet frame0456 4) = E.orient mixed045 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have hrule : seed5TwoMixedRule false false
      (E.orient mixed045) (E.orient mixed046) (E.orient mixed056) (E.orient mixed456) :=
    seed5TwoMixedRule_of_admissible E frame0456 false false
      (E.orient mixed045) (E.orient mixed046) (E.orient mixed056) (E.orient mixed456)
      h0 h1 h2 h3 h4 h5 (hE frame0456)
  change seed5TwoRuleSame (E.orient mixed045) (E.orient mixed046) (E.orient mixed056) (E.orient mixed456)
  simpa [seed5TwoMixedRule] using hrule

/-- Mixed packet 1236 satisfies its exact permitted six-facet Boolean rule. -/
private theorem mixedRule1236
    (E : Hyper 5 (Fin 9))
    (hE : Admissible ({0,3} : Set ℕ) E)
    (hL : Preserves seed5TwoLeft E (leftJointInclusion 7))
    (hR : Preserves seed5TwoRight E (rightJointInclusion 7)) :
    seed5TwoRuleOneZero ((seed5TwoMixedBits E) 15) ((seed5TwoMixedBits E) 18) ((seed5TwoMixedBits E) 21) ((seed5TwoMixedBits E) 27) := by
  have h0 : E.orient (facet frame1236 0) = true := by
    calc
      E.orient (facet frame1236 0) =
          E.orient (right1236.trans (rightJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoRight.orient right1236 := hR right1236
      _ = true := by
        have hm : StrictMono (right1236 : Fin 5 → Fin 8) := by decide
        change (Hyper.fromOrderedSigns seed5TwoRightSigns).orient right1236 = true
        rw [fromOrderedSigns_orient_strictMono seed5TwoRightSigns right1236 hm]
        decide
  have h5 : E.orient (facet frame1236 5) = false := by
    calc
      E.orient (facet frame1236 5) =
          E.orient (left1236.trans (leftJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoLeft.orient left1236 := hL left1236
      _ = false := by
        calc
          seed5TwoLeft.orient left1236 =
              seed5TwoLeftSigns (tupleVertices right1236) :=
            seed5Two_left_rotated left1236 right1236
              (by ext i; fin_cases i <;> decide) (by decide)
          _ = false := by decide
  have h1 : E.orient (facet frame1236 1) = E.orient mixed236 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h2 : E.orient (facet frame1236 2) = E.orient mixed136 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h3 : E.orient (facet frame1236 3) = E.orient mixed126 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h4 : E.orient (facet frame1236 4) = E.orient mixed123 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have hrule : seed5TwoMixedRule true false
      (E.orient mixed123) (E.orient mixed126) (E.orient mixed136) (E.orient mixed236) :=
    seed5TwoMixedRule_of_admissible E frame1236 true false
      (E.orient mixed123) (E.orient mixed126) (E.orient mixed136) (E.orient mixed236)
      h0 h1 h2 h3 h4 h5 (hE frame1236)
  change seed5TwoRuleOneZero (E.orient mixed123) (E.orient mixed126) (E.orient mixed136) (E.orient mixed236)
  simpa [seed5TwoMixedRule] using hrule

/-- Mixed packet 1246 satisfies its exact permitted six-facet Boolean rule. -/
private theorem mixedRule1246
    (E : Hyper 5 (Fin 9))
    (hE : Admissible ({0,3} : Set ℕ) E)
    (hL : Preserves seed5TwoLeft E (leftJointInclusion 7))
    (hR : Preserves seed5TwoRight E (rightJointInclusion 7)) :
    seed5TwoRuleSame ((seed5TwoMixedBits E) 16) ((seed5TwoMixedBits E) 18) ((seed5TwoMixedBits E) 23) ((seed5TwoMixedBits E) 29) := by
  have h0 : E.orient (facet frame1246 0) = false := by
    calc
      E.orient (facet frame1246 0) =
          E.orient (right1246.trans (rightJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoRight.orient right1246 := hR right1246
      _ = false := by
        have hm : StrictMono (right1246 : Fin 5 → Fin 8) := by decide
        change (Hyper.fromOrderedSigns seed5TwoRightSigns).orient right1246 = false
        rw [fromOrderedSigns_orient_strictMono seed5TwoRightSigns right1246 hm]
        decide
  have h5 : E.orient (facet frame1246 5) = false := by
    calc
      E.orient (facet frame1246 5) =
          E.orient (left1246.trans (leftJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoLeft.orient left1246 := hL left1246
      _ = false := by
        calc
          seed5TwoLeft.orient left1246 =
              seed5TwoLeftSigns (tupleVertices right1246) :=
            seed5Two_left_rotated left1246 right1246
              (by ext i; fin_cases i <;> decide) (by decide)
          _ = false := by decide
  have h1 : E.orient (facet frame1246 1) = E.orient mixed246 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h2 : E.orient (facet frame1246 2) = E.orient mixed146 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h3 : E.orient (facet frame1246 3) = E.orient mixed126 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h4 : E.orient (facet frame1246 4) = E.orient mixed124 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have hrule : seed5TwoMixedRule false false
      (E.orient mixed124) (E.orient mixed126) (E.orient mixed146) (E.orient mixed246) :=
    seed5TwoMixedRule_of_admissible E frame1246 false false
      (E.orient mixed124) (E.orient mixed126) (E.orient mixed146) (E.orient mixed246)
      h0 h1 h2 h3 h4 h5 (hE frame1246)
  change seed5TwoRuleSame (E.orient mixed124) (E.orient mixed126) (E.orient mixed146) (E.orient mixed246)
  simpa [seed5TwoMixedRule] using hrule

/-- Mixed packet 1256 satisfies its exact permitted six-facet Boolean rule. -/
private theorem mixedRule1256
    (E : Hyper 5 (Fin 9))
    (hE : Admissible ({0,3} : Set ℕ) E)
    (hL : Preserves seed5TwoLeft E (leftJointInclusion 7))
    (hR : Preserves seed5TwoRight E (rightJointInclusion 7)) :
    seed5TwoRuleSame ((seed5TwoMixedBits E) 17) ((seed5TwoMixedBits E) 18) ((seed5TwoMixedBits E) 24) ((seed5TwoMixedBits E) 30) := by
  have h0 : E.orient (facet frame1256 0) = false := by
    calc
      E.orient (facet frame1256 0) =
          E.orient (right1256.trans (rightJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoRight.orient right1256 := hR right1256
      _ = false := by
        have hm : StrictMono (right1256 : Fin 5 → Fin 8) := by decide
        change (Hyper.fromOrderedSigns seed5TwoRightSigns).orient right1256 = false
        rw [fromOrderedSigns_orient_strictMono seed5TwoRightSigns right1256 hm]
        decide
  have h5 : E.orient (facet frame1256 5) = false := by
    calc
      E.orient (facet frame1256 5) =
          E.orient (left1256.trans (leftJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoLeft.orient left1256 := hL left1256
      _ = false := by
        calc
          seed5TwoLeft.orient left1256 =
              seed5TwoLeftSigns (tupleVertices right1256) :=
            seed5Two_left_rotated left1256 right1256
              (by ext i; fin_cases i <;> decide) (by decide)
          _ = false := by decide
  have h1 : E.orient (facet frame1256 1) = E.orient mixed256 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h2 : E.orient (facet frame1256 2) = E.orient mixed156 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h3 : E.orient (facet frame1256 3) = E.orient mixed126 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h4 : E.orient (facet frame1256 4) = E.orient mixed125 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have hrule : seed5TwoMixedRule false false
      (E.orient mixed125) (E.orient mixed126) (E.orient mixed156) (E.orient mixed256) :=
    seed5TwoMixedRule_of_admissible E frame1256 false false
      (E.orient mixed125) (E.orient mixed126) (E.orient mixed156) (E.orient mixed256)
      h0 h1 h2 h3 h4 h5 (hE frame1256)
  change seed5TwoRuleSame (E.orient mixed125) (E.orient mixed126) (E.orient mixed156) (E.orient mixed256)
  simpa [seed5TwoMixedRule] using hrule

/-- Mixed packet 1345 satisfies its exact permitted six-facet Boolean rule. -/
private theorem mixedRule1345
    (E : Hyper 5 (Fin 9))
    (hE : Admissible ({0,3} : Set ℕ) E)
    (hL : Preserves seed5TwoLeft E (leftJointInclusion 7))
    (hR : Preserves seed5TwoRight E (rightJointInclusion 7)) :
    seed5TwoRuleSame ((seed5TwoMixedBits E) 19) ((seed5TwoMixedBits E) 20) ((seed5TwoMixedBits E) 22) ((seed5TwoMixedBits E) 31) := by
  have h0 : E.orient (facet frame1345 0) = true := by
    calc
      E.orient (facet frame1345 0) =
          E.orient (right1345.trans (rightJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoRight.orient right1345 := hR right1345
      _ = true := by
        have hm : StrictMono (right1345 : Fin 5 → Fin 8) := by decide
        change (Hyper.fromOrderedSigns seed5TwoRightSigns).orient right1345 = true
        rw [fromOrderedSigns_orient_strictMono seed5TwoRightSigns right1345 hm]
        decide
  have h5 : E.orient (facet frame1345 5) = true := by
    calc
      E.orient (facet frame1345 5) =
          E.orient (left1345.trans (leftJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoLeft.orient left1345 := hL left1345
      _ = true := by
        calc
          seed5TwoLeft.orient left1345 =
              seed5TwoLeftSigns (tupleVertices right1345) :=
            seed5Two_left_rotated left1345 right1345
              (by ext i; fin_cases i <;> decide) (by decide)
          _ = true := by decide
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
  have hrule : seed5TwoMixedRule true true
      (E.orient mixed134) (E.orient mixed135) (E.orient mixed145) (E.orient mixed345) :=
    seed5TwoMixedRule_of_admissible E frame1345 true true
      (E.orient mixed134) (E.orient mixed135) (E.orient mixed145) (E.orient mixed345)
      h0 h1 h2 h3 h4 h5 (hE frame1345)
  change seed5TwoRuleSame (E.orient mixed134) (E.orient mixed135) (E.orient mixed145) (E.orient mixed345)
  simpa [seed5TwoMixedRule] using hrule

/-- Mixed packet 1356 satisfies its exact permitted six-facet Boolean rule. -/
private theorem mixedRule1356
    (E : Hyper 5 (Fin 9))
    (hE : Admissible ({0,3} : Set ℕ) E)
    (hL : Preserves seed5TwoLeft E (leftJointInclusion 7))
    (hR : Preserves seed5TwoRight E (rightJointInclusion 7)) :
    seed5TwoRuleOneZero ((seed5TwoMixedBits E) 20) ((seed5TwoMixedBits E) 21) ((seed5TwoMixedBits E) 24) ((seed5TwoMixedBits E) 33) := by
  have h0 : E.orient (facet frame1356 0) = true := by
    calc
      E.orient (facet frame1356 0) =
          E.orient (right1356.trans (rightJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoRight.orient right1356 := hR right1356
      _ = true := by
        have hm : StrictMono (right1356 : Fin 5 → Fin 8) := by decide
        change (Hyper.fromOrderedSigns seed5TwoRightSigns).orient right1356 = true
        rw [fromOrderedSigns_orient_strictMono seed5TwoRightSigns right1356 hm]
        decide
  have h5 : E.orient (facet frame1356 5) = false := by
    calc
      E.orient (facet frame1356 5) =
          E.orient (left1356.trans (leftJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoLeft.orient left1356 := hL left1356
      _ = false := by
        calc
          seed5TwoLeft.orient left1356 =
              seed5TwoLeftSigns (tupleVertices right1356) :=
            seed5Two_left_rotated left1356 right1356
              (by ext i; fin_cases i <;> decide) (by decide)
          _ = false := by decide
  have h1 : E.orient (facet frame1356 1) = E.orient mixed356 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h2 : E.orient (facet frame1356 2) = E.orient mixed156 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h3 : E.orient (facet frame1356 3) = E.orient mixed136 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h4 : E.orient (facet frame1356 4) = E.orient mixed135 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have hrule : seed5TwoMixedRule true false
      (E.orient mixed135) (E.orient mixed136) (E.orient mixed156) (E.orient mixed356) :=
    seed5TwoMixedRule_of_admissible E frame1356 true false
      (E.orient mixed135) (E.orient mixed136) (E.orient mixed156) (E.orient mixed356)
      h0 h1 h2 h3 h4 h5 (hE frame1356)
  change seed5TwoRuleOneZero (E.orient mixed135) (E.orient mixed136) (E.orient mixed156) (E.orient mixed356)
  simpa [seed5TwoMixedRule] using hrule

/-- Mixed packet 1456 satisfies its exact permitted six-facet Boolean rule. -/
private theorem mixedRule1456
    (E : Hyper 5 (Fin 9))
    (hE : Admissible ({0,3} : Set ℕ) E)
    (hL : Preserves seed5TwoLeft E (leftJointInclusion 7))
    (hR : Preserves seed5TwoRight E (rightJointInclusion 7)) :
    seed5TwoRuleOneZero ((seed5TwoMixedBits E) 22) ((seed5TwoMixedBits E) 23) ((seed5TwoMixedBits E) 24) ((seed5TwoMixedBits E) 34) := by
  have h0 : E.orient (facet frame1456 0) = true := by
    calc
      E.orient (facet frame1456 0) =
          E.orient (right1456.trans (rightJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoRight.orient right1456 := hR right1456
      _ = true := by
        have hm : StrictMono (right1456 : Fin 5 → Fin 8) := by decide
        change (Hyper.fromOrderedSigns seed5TwoRightSigns).orient right1456 = true
        rw [fromOrderedSigns_orient_strictMono seed5TwoRightSigns right1456 hm]
        decide
  have h5 : E.orient (facet frame1456 5) = false := by
    calc
      E.orient (facet frame1456 5) =
          E.orient (left1456.trans (leftJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoLeft.orient left1456 := hL left1456
      _ = false := by
        calc
          seed5TwoLeft.orient left1456 =
              seed5TwoLeftSigns (tupleVertices right1456) :=
            seed5Two_left_rotated left1456 right1456
              (by ext i; fin_cases i <;> decide) (by decide)
          _ = false := by decide
  have h1 : E.orient (facet frame1456 1) = E.orient mixed456 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h2 : E.orient (facet frame1456 2) = E.orient mixed156 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h3 : E.orient (facet frame1456 3) = E.orient mixed146 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h4 : E.orient (facet frame1456 4) = E.orient mixed145 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have hrule : seed5TwoMixedRule true false
      (E.orient mixed145) (E.orient mixed146) (E.orient mixed156) (E.orient mixed456) :=
    seed5TwoMixedRule_of_admissible E frame1456 true false
      (E.orient mixed145) (E.orient mixed146) (E.orient mixed156) (E.orient mixed456)
      h0 h1 h2 h3 h4 h5 (hE frame1456)
  change seed5TwoRuleOneZero (E.orient mixed145) (E.orient mixed146) (E.orient mixed156) (E.orient mixed456)
  simpa [seed5TwoMixedRule] using hrule

/-- Mixed packet 2345 satisfies its exact permitted six-facet Boolean rule. -/
private theorem mixedRule2345
    (E : Hyper 5 (Fin 9))
    (hE : Admissible ({0,3} : Set ℕ) E)
    (hL : Preserves seed5TwoLeft E (leftJointInclusion 7))
    (hR : Preserves seed5TwoRight E (rightJointInclusion 7)) :
    seed5TwoRuleSame ((seed5TwoMixedBits E) 25) ((seed5TwoMixedBits E) 26) ((seed5TwoMixedBits E) 28) ((seed5TwoMixedBits E) 31) := by
  have h0 : E.orient (facet frame2345 0) = false := by
    calc
      E.orient (facet frame2345 0) =
          E.orient (right2345.trans (rightJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoRight.orient right2345 := hR right2345
      _ = false := by
        have hm : StrictMono (right2345 : Fin 5 → Fin 8) := by decide
        change (Hyper.fromOrderedSigns seed5TwoRightSigns).orient right2345 = false
        rw [fromOrderedSigns_orient_strictMono seed5TwoRightSigns right2345 hm]
        decide
  have h5 : E.orient (facet frame2345 5) = false := by
    calc
      E.orient (facet frame2345 5) =
          E.orient (left2345.trans (leftJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoLeft.orient left2345 := hL left2345
      _ = false := by
        calc
          seed5TwoLeft.orient left2345 =
              seed5TwoLeftSigns (tupleVertices right2345) :=
            seed5Two_left_rotated left2345 right2345
              (by ext i; fin_cases i <;> decide) (by decide)
          _ = false := by decide
  have h1 : E.orient (facet frame2345 1) = E.orient mixed345 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h2 : E.orient (facet frame2345 2) = E.orient mixed245 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h3 : E.orient (facet frame2345 3) = E.orient mixed235 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h4 : E.orient (facet frame2345 4) = E.orient mixed234 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have hrule : seed5TwoMixedRule false false
      (E.orient mixed234) (E.orient mixed235) (E.orient mixed245) (E.orient mixed345) :=
    seed5TwoMixedRule_of_admissible E frame2345 false false
      (E.orient mixed234) (E.orient mixed235) (E.orient mixed245) (E.orient mixed345)
      h0 h1 h2 h3 h4 h5 (hE frame2345)
  change seed5TwoRuleSame (E.orient mixed234) (E.orient mixed235) (E.orient mixed245) (E.orient mixed345)
  simpa [seed5TwoMixedRule] using hrule

/-- Mixed packet 2346 satisfies its exact permitted six-facet Boolean rule. -/
private theorem mixedRule2346
    (E : Hyper 5 (Fin 9))
    (hE : Admissible ({0,3} : Set ℕ) E)
    (hL : Preserves seed5TwoLeft E (leftJointInclusion 7))
    (hR : Preserves seed5TwoRight E (rightJointInclusion 7)) :
    seed5TwoRuleOneZero ((seed5TwoMixedBits E) 25) ((seed5TwoMixedBits E) 27) ((seed5TwoMixedBits E) 29) ((seed5TwoMixedBits E) 32) := by
  have h0 : E.orient (facet frame2346 0) = true := by
    calc
      E.orient (facet frame2346 0) =
          E.orient (right2346.trans (rightJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoRight.orient right2346 := hR right2346
      _ = true := by
        have hm : StrictMono (right2346 : Fin 5 → Fin 8) := by decide
        change (Hyper.fromOrderedSigns seed5TwoRightSigns).orient right2346 = true
        rw [fromOrderedSigns_orient_strictMono seed5TwoRightSigns right2346 hm]
        decide
  have h5 : E.orient (facet frame2346 5) = false := by
    calc
      E.orient (facet frame2346 5) =
          E.orient (left2346.trans (leftJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoLeft.orient left2346 := hL left2346
      _ = false := by
        calc
          seed5TwoLeft.orient left2346 =
              seed5TwoLeftSigns (tupleVertices right2346) :=
            seed5Two_left_rotated left2346 right2346
              (by ext i; fin_cases i <;> decide) (by decide)
          _ = false := by decide
  have h1 : E.orient (facet frame2346 1) = E.orient mixed346 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h2 : E.orient (facet frame2346 2) = E.orient mixed246 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h3 : E.orient (facet frame2346 3) = E.orient mixed236 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h4 : E.orient (facet frame2346 4) = E.orient mixed234 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have hrule : seed5TwoMixedRule true false
      (E.orient mixed234) (E.orient mixed236) (E.orient mixed246) (E.orient mixed346) :=
    seed5TwoMixedRule_of_admissible E frame2346 true false
      (E.orient mixed234) (E.orient mixed236) (E.orient mixed246) (E.orient mixed346)
      h0 h1 h2 h3 h4 h5 (hE frame2346)
  change seed5TwoRuleOneZero (E.orient mixed234) (E.orient mixed236) (E.orient mixed246) (E.orient mixed346)
  simpa [seed5TwoMixedRule] using hrule

/-- Mixed packet 2456 satisfies its exact permitted six-facet Boolean rule. -/
private theorem mixedRule2456
    (E : Hyper 5 (Fin 9))
    (hE : Admissible ({0,3} : Set ℕ) E)
    (hL : Preserves seed5TwoLeft E (leftJointInclusion 7))
    (hR : Preserves seed5TwoRight E (rightJointInclusion 7)) :
    seed5TwoRuleSame ((seed5TwoMixedBits E) 28) ((seed5TwoMixedBits E) 29) ((seed5TwoMixedBits E) 30) ((seed5TwoMixedBits E) 34) := by
  have h0 : E.orient (facet frame2456 0) = false := by
    calc
      E.orient (facet frame2456 0) =
          E.orient (right2456.trans (rightJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoRight.orient right2456 := hR right2456
      _ = false := by
        have hm : StrictMono (right2456 : Fin 5 → Fin 8) := by decide
        change (Hyper.fromOrderedSigns seed5TwoRightSigns).orient right2456 = false
        rw [fromOrderedSigns_orient_strictMono seed5TwoRightSigns right2456 hm]
        decide
  have h5 : E.orient (facet frame2456 5) = false := by
    calc
      E.orient (facet frame2456 5) =
          E.orient (left2456.trans (leftJointInclusion 7)) := by
            congr 1
            ext i
            fin_cases i <;> decide
      _ = seed5TwoLeft.orient left2456 := hL left2456
      _ = false := by
        calc
          seed5TwoLeft.orient left2456 =
              seed5TwoLeftSigns (tupleVertices right2456) :=
            seed5Two_left_rotated left2456 right2456
              (by ext i; fin_cases i <;> decide) (by decide)
          _ = false := by decide
  have h1 : E.orient (facet frame2456 1) = E.orient mixed456 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h2 : E.orient (facet frame2456 2) = E.orient mixed256 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h3 : E.orient (facet frame2456 3) = E.orient mixed246 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have h4 : E.orient (facet frame2456 4) = E.orient mixed245 := by
    congr 1
    ext i
    fin_cases i <;> decide
  have hrule : seed5TwoMixedRule false false
      (E.orient mixed245) (E.orient mixed246) (E.orient mixed256) (E.orient mixed456) :=
    seed5TwoMixedRule_of_admissible E frame2456 false false
      (E.orient mixed245) (E.orient mixed246) (E.orient mixed256) (E.orient mixed456)
      h0 h1 h2 h3 h4 h5 (hE frame2456)
  change seed5TwoRuleSame (E.orient mixed245) (E.orient mixed246) (E.orient mixed256) (E.orient mixed456)
  simpa [seed5TwoMixedRule] using hrule

/-- The twenty actual local packets force the already verified
35-variable Boolean contradiction; no distinct-new-vertex
amalgam of the displayed sides exists. -/
theorem seed5Two_no_joint
    (E : Hyper 5 (Fin 9))
    (hE : Admissible ({0,3} : Set ℕ) E)
    (hL : Preserves seed5TwoLeft E (leftJointInclusion 7))
    (hR : Preserves seed5TwoRight E (rightJointInclusion 7)) :
    False := by
  exact seed5Two_mixed_boolean_unsat (seed5TwoMixedBits E)
    (mixedRule0125 E hE hL hR)
    (mixedRule0134 E hE hL hR)
    (mixedRule0136 E hE hL hR)
    (mixedRule0156 E hE hL hR)
    (mixedRule0235 E hE hL hR)
    (mixedRule0236 E hE hL hR)
    (mixedRule0246 E hE hL hR)
    (mixedRule0256 E hE hL hR)
    (mixedRule0345 E hE hL hR)
    (mixedRule0356 E hE hL hR)
    (mixedRule0456 E hE hL hR)
    (mixedRule1236 E hE hL hR)
    (mixedRule1246 E hE hL hR)
    (mixedRule1256 E hE hL hR)
    (mixedRule1345 E hE hL hR)
    (mixedRule1356 E hE hL hR)
    (mixedRule1456 E hE hL hR)
    (mixedRule2345 E hE hL hR)
    (mixedRule2346 E hE hL hR)
    (mixedRule2456 E hE hL hR)

/-- The two one-point extensions disagree on the four-set link
0123, hence their new vertices cannot be identified. -/
theorem seed5Two_disagreement :
    ∃ t : Fin 5 ↪ Fin 8,
      seed5TwoLeft.orient t ≠ seed5TwoRight.orient t := by
  let t : Fin 5 ↪ Fin 8 := ⟨![0,1,2,3,7], by decide⟩
  refine ⟨t, ?_⟩
  have ht : StrictMono (t : Fin 5 → Fin 8) := by decide
  change (Hyper.fromOrderedSigns seed5TwoLeftSigns).orient t ≠
    (Hyper.fromOrderedSigns seed5TwoRightSigns).orient t
  rw [fromOrderedSigns_orient_strictMono seed5TwoLeftSigns t ht,
    fromOrderedSigns_orient_strictMono seed5TwoRightSigns t ht]
  decide

/-- Genuine ordinary, not merely strong, non-amalgamation
in the arity-five class allowing precisely local types 0 and 3. -/
theorem seed5Two_not_hasAP :
    ¬ HasAP 5 ({0,3} : Set ℕ) := by
  apply not_hasAP_of_no_joint
    seed5TwoBase seed5TwoLeft seed5TwoRight
    seed5Two_base_admissible seed5Two_left_admissible
    seed5Two_right_admissible seed5Two_base_left seed5Two_base_right
    seed5Two_disagreement
  intro E hE hL hR
  exact seed5Two_no_joint E hE hL hR

end Hypertournaments
