import Hypertournaments.GeneralDirectPacket
import Hypertournaments.Obstruction

/-!
# First arity-five finite seed: the {T_{5,0}, T_{5,3}} class

These are the exact seven-old-vertex sign tables in Section 4 of
negative_general_arity_audit_v4.tex.  They are only finite data; the
non-amalgamation argument will require a separate mixed-packet proof.

The new vertex is 7 on both sides. Moving the left new vertex from
the first position to the last crosses four base vertices, so unlike
the arity-four seeds the left-link signs are NOT complemented.
-/

namespace Hypertournaments

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Positive five-set signs on the seven old vertices. -/
def seed5TwoOldPlus7 : Finset (Finset (Fin 7)) :=
  { {0,1,2,3,5}, {0,1,2,4,6}, {0,1,3,5,6},
    {0,2,3,4,5}, {0,2,4,5,6}, {1,2,3,4,6},
    {1,3,4,5,6} }

def seed5TwoOldPlus8 : Finset (Finset (Fin 8)) :=
  { {0,1,2,3,5}, {0,1,2,4,6}, {0,1,3,5,6},
    {0,2,3,4,5}, {0,2,4,5,6}, {1,2,3,4,6},
    {1,3,4,5,6} }

/-- Positive four-set link of the left new vertex. -/
def seed5TwoAlphaPlus8 : Finset (Finset (Fin 8)) :=
  { {0,1,2,3}, {0,1,2,4}, {0,1,2,5}, {0,1,2,6},
    {0,1,3,5}, {0,1,4,5}, {0,1,4,6}, {0,2,3,4},
    {0,2,4,5}, {0,3,4,5}, {0,3,4,6}, {1,2,3,4},
    {1,3,4,5} }

/-- Positive four-set link of the right new vertex. -/
def seed5TwoBetaPlus8 : Finset (Finset (Fin 8)) :=
  { {0,1,2,4}, {0,1,3,4}, {0,1,4,5}, {0,1,5,6},
    {0,2,3,4}, {0,2,3,6}, {0,2,5,6}, {0,3,4,6},
    {0,3,5,6}, {1,2,3,4}, {1,2,3,5}, {1,2,3,6},
    {1,2,4,5}, {1,3,4,5}, {1,3,5,6}, {1,4,5,6},
    {2,3,4,6}, {2,3,5,6} }

def seed5TwoBaseSigns (Q : Finset (Fin 7)) : Bool :=
  decide (Q ∈ seed5TwoOldPlus7)

def seed5TwoLeftSigns (Q : Finset (Fin 8)) : Bool :=
  if (7 : Fin 8) ∈ Q then
    decide (Q.erase 7 ∈ seed5TwoAlphaPlus8)
  else
    decide (Q ∈ seed5TwoOldPlus8)

def seed5TwoRightSigns (Q : Finset (Fin 8)) : Bool :=
  if (7 : Fin 8) ∈ Q then
    decide (Q.erase 7 ∈ seed5TwoBetaPlus8)
  else
    decide (Q ∈ seed5TwoOldPlus8)

def seed5TwoBase : Hyper 5 (Fin 7) :=
  Hyper.fromOrderedSigns seed5TwoBaseSigns

def seed5TwoLeft : Hyper 5 (Fin 8) :=
  Hyper.fromOrderedSigns seed5TwoLeftSigns

def seed5TwoRight : Hyper 5 (Fin 8) :=
  Hyper.fromOrderedSigns seed5TwoRightSigns

/-- The finite sign tables agree over the seven old vertices. -/
theorem seed5Two_base_left :
    Preserves seed5TwoBase seed5TwoLeft (onePointBaseEmbedding 7) := by
  have ht : ∀ Q : Finset (Fin 7),
      seed5TwoLeftSigns (Q.image (Fin.castSuccOrderEmb : Fin 7 ↪o Fin 8)) =
        seed5TwoBaseSigns Q := by
    decide
  exact fromOrderedSigns_preserves
    (g := (Fin.castSuccOrderEmb : Fin 7 ↪o Fin 8))
    seed5TwoBaseSigns seed5TwoLeftSigns ht

theorem seed5Two_base_right :
    Preserves seed5TwoBase seed5TwoRight (onePointBaseEmbedding 7) := by
  have ht : ∀ Q : Finset (Fin 7),
      seed5TwoRightSigns (Q.image (Fin.castSuccOrderEmb : Fin 7 ↪o Fin 8)) =
        seed5TwoBaseSigns Q := by
    decide
  exact fromOrderedSigns_preserves
    (g := (Fin.castSuccOrderEmb : Fin 7 ↪o Fin 8))
    seed5TwoBaseSigns seed5TwoRightSigns ht

/-- Finite six-set checker for the two allowed local types. -/
def directZeroThree5 {k : ℕ}
    (signs : Finset (Fin k) → Bool) (Q : Finset (Fin k)) : Prop :=
  Q.card = 6 →
    let c := directFacetPositiveCount signs Q
    min c (6 - c) = 0 ∨ min c (6 - c) = 3

theorem seed5Two_base_direct :
    ∀ Q : Finset (Fin 7), directZeroThree5 seed5TwoBaseSigns Q := by
  unfold directZeroThree5 directFacetPositiveCount
  decide +kernel

theorem seed5Two_left_direct :
    ∀ Q : Finset (Fin 8), directZeroThree5 seed5TwoLeftSigns Q := by
  unfold directZeroThree5 directFacetPositiveCount
  decide +kernel

theorem seed5Two_right_direct :
    ∀ Q : Finset (Fin 8), directZeroThree5 seed5TwoRightSigns Q := by
  unfold directZeroThree5 directFacetPositiveCount
  decide +kernel

/-- Full ordinary admissibility, not merely canonical six-set checks. -/
theorem seed5Two_base_admissible :
    Admissible ({0,3} : Set ℕ) seed5TwoBase := by
  apply fromOrderedSigns_admissible_five_of_direct_count seed5TwoBaseSigns {0,3}
  intro Q hQ
  have h := seed5Two_base_direct Q hQ
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h

theorem seed5Two_left_admissible :
    Admissible ({0,3} : Set ℕ) seed5TwoLeft := by
  apply fromOrderedSigns_admissible_five_of_direct_count seed5TwoLeftSigns {0,3}
  intro Q hQ
  have h := seed5Two_left_direct Q hQ
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h

theorem seed5Two_right_admissible :
    Admissible ({0,3} : Set ℕ) seed5TwoRight := by
  apply fromOrderedSigns_admissible_five_of_direct_count seed5TwoRightSigns {0,3}
  intro Q hQ
  have h := seed5Two_right_direct Q hQ
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h

end Hypertournaments
