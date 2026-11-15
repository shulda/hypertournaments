import Hypertournaments.FourDirectAdmissible

/-!
# The arity-four one-point obstruction omitting T_{4,1}

Literal tables from the mathematical technical note:
  base plus: 1245
  alpha plus: 035,135,235,345
  gamma plus: 012,034,035,045,134,245,345
where gamma=-beta.

For each one-point extension the new point is placed last as vertex 6,
so both links have their orientation sign complemented as explained
above. The local types allowed are 0 and 2.

The non-amalgamation proof will be added separately.
-/

namespace Hypertournaments

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

private def forbidOneOldPlus6 : Finset (Fin 6) := {1,2,4,5}
private def forbidOneOldPlus7 : Finset (Fin 7) := {1,2,4,5}

private def forbidOneAlphaPlus : Finset (Finset (Fin 7)) :=
  { {0,3,5}, {1,3,5}, {2,3,5}, {3,4,5} }

private def forbidOneGammaPlus : Finset (Finset (Fin 7)) :=
  { {0,1,2}, {0,3,4}, {0,3,5}, {0,4,5},
    {1,3,4}, {2,4,5}, {3,4,5} }

def forbidOneBaseSigns (Q : Finset (Fin 6)) : Bool :=
  decide (Q = forbidOneOldPlus6)

def forbidOneLeftSigns (Q : Finset (Fin 7)) : Bool :=
  if (6 : Fin 7) ∈ Q then
    !(decide (Q.erase 6 ∈ forbidOneAlphaPlus))
  else
    decide (Q = forbidOneOldPlus7)

def forbidOneRightSigns (Q : Finset (Fin 7)) : Bool :=
  if (6 : Fin 7) ∈ Q then
    !(decide (Q.erase 6 ∈ forbidOneGammaPlus))
  else
    decide (Q = forbidOneOldPlus7)

def forbidOneBase : Hyper 4 (Fin 6) :=
  Hyper.fromOrderedSigns forbidOneBaseSigns
def forbidOneLeft : Hyper 4 (Fin 7) :=
  Hyper.fromOrderedSigns forbidOneLeftSigns
def forbidOneRight : Hyper 4 (Fin 7) :=
  Hyper.fromOrderedSigns forbidOneRightSigns

theorem forbidOne_base_left :
    Preserves forbidOneBase forbidOneLeft (onePointBaseEmbedding 6) := by
  have ht : ∀ Q : Finset (Fin 6),
      forbidOneLeftSigns (Q.image (Fin.castSuccOrderEmb : Fin 6 ↪o Fin 7)) =
        forbidOneBaseSigns Q := by
    decide
  exact fromOrderedSigns_preserves
    (g := (Fin.castSuccOrderEmb : Fin 6 ↪o Fin 7))
    forbidOneBaseSigns forbidOneLeftSigns ht

theorem forbidOne_base_right :
    Preserves forbidOneBase forbidOneRight (onePointBaseEmbedding 6) := by
  have ht : ∀ Q : Finset (Fin 6),
      forbidOneRightSigns (Q.image (Fin.castSuccOrderEmb : Fin 6 ↪o Fin 7)) =
        forbidOneBaseSigns Q := by
    decide
  exact fromOrderedSigns_preserves
    (g := (Fin.castSuccOrderEmb : Fin 6 ↪o Fin 7))
    forbidOneBaseSigns forbidOneRightSigns ht

def directZeroTwo4 {k : ℕ}
    (signs : Finset (Fin k) → Bool) (Q : Finset (Fin k)) : Prop :=
  Q.card = 5 →
    let c := directFacetPositiveCount signs Q
    min c (5 - c) = 0 ∨ min c (5 - c) = 2

theorem forbidOne_base_direct :
    ∀ Q : Finset (Fin 6), directZeroTwo4 forbidOneBaseSigns Q := by
  unfold directZeroTwo4 directFacetPositiveCount
  decide +kernel

theorem forbidOne_left_direct :
    ∀ Q : Finset (Fin 7), directZeroTwo4 forbidOneLeftSigns Q := by
  unfold directZeroTwo4 directFacetPositiveCount
  decide +kernel

theorem forbidOne_right_direct :
    ∀ Q : Finset (Fin 7), directZeroTwo4 forbidOneRightSigns Q := by
  unfold directZeroTwo4 directFacetPositiveCount
  decide +kernel

theorem forbidOne_base_admissible :
    Admissible ({0,2} : Set ℕ) forbidOneBase := by
  apply fromOrderedSigns_admissible_of_direct forbidOneBaseSigns {0,2}
  intro Q hQ
  have h := forbidOne_base_direct Q hQ
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h

theorem forbidOne_left_admissible :
    Admissible ({0,2} : Set ℕ) forbidOneLeft := by
  apply fromOrderedSigns_admissible_of_direct forbidOneLeftSigns {0,2}
  intro Q hQ
  have h := forbidOne_left_direct Q hQ
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h

theorem forbidOne_right_admissible :
    Admissible ({0,2} : Set ℕ) forbidOneRight := by
  apply fromOrderedSigns_admissible_of_direct forbidOneRightSigns {0,2}
  intro Q hQ
  have h := forbidOne_right_direct Q hQ
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h

end Hypertournaments
