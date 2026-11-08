import Hypertournaments.GeneralDirectPacket
import Hypertournaments.Obstruction

/-!
# The arity-five {0,1,3} exceptional one-point diagram

This is the k=0 instance of the uniform 1 mod 4 obstruction in
notes/negative_general_arity_audit_v4.tex, Section "critical classes
in arities 1 mod 4".

The six base vertices are 0,...,5. The two new vertices are both
numbered 6 in their respective one-point extensions. The source
raw bit e=0 denotes a positive increasing orientation; consequently
we list the *complements* of the positive omitted-pair sets.

Moving the left new vertex from the start of a five-tuple to its
last position crosses four base vertices and does not change sign.
The displayed tables therefore match the paper without a
sign flip.

At this stage the three finite structures and their admissibility
are checked. Failure of ordinary AP is proved separately.
-/

namespace Hypertournaments

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- The positive base five-sets (omitted vertices 2 or 4). -/
def seed5ExtraOldPlus6 : Finset (Finset (Fin 6)) :=
  { {0,1,3,4,5}, {0,1,2,3,5} }

def seed5ExtraOldPlus7 : Finset (Finset (Fin 7)) :=
  { {0,1,3,4,5}, {0,1,2,3,5} }

/-- The positive left link four-sets: omitted pairs 14,15,24,34,35. -/
def seed5ExtraAlphaPlus7 : Finset (Finset (Fin 7)) :=
  { {0,2,3,5}, {0,2,3,4}, {0,1,3,5},
    {0,1,2,5}, {0,1,2,4} }

/-- The positive right link four-sets: omitted pairs 01,03,05,14,25,34. -/
def seed5ExtraBetaPlus7 : Finset (Finset (Fin 7)) :=
  { {2,3,4,5}, {1,2,4,5}, {1,2,3,4},
    {0,2,3,5}, {0,1,3,4}, {0,1,2,5} }

def seed5ExtraBaseSigns (Q : Finset (Fin 6)) : Bool :=
  decide (Q ∈ seed5ExtraOldPlus6)

def seed5ExtraLeftSigns (Q : Finset (Fin 7)) : Bool :=
  if (6 : Fin 7) ∈ Q then
    decide (Q.erase 6 ∈ seed5ExtraAlphaPlus7)
  else
    decide (Q ∈ seed5ExtraOldPlus7)

def seed5ExtraRightSigns (Q : Finset (Fin 7)) : Bool :=
  if (6 : Fin 7) ∈ Q then
    decide (Q.erase 6 ∈ seed5ExtraBetaPlus7)
  else
    decide (Q ∈ seed5ExtraOldPlus7)

def seed5ExtraBase : Hyper 5 (Fin 6) :=
  Hyper.fromOrderedSigns seed5ExtraBaseSigns

def seed5ExtraLeft : Hyper 5 (Fin 7) :=
  Hyper.fromOrderedSigns seed5ExtraLeftSigns

def seed5ExtraRight : Hyper 5 (Fin 7) :=
  Hyper.fromOrderedSigns seed5ExtraRightSigns

theorem seed5Extra_base_left :
    Preserves seed5ExtraBase seed5ExtraLeft (onePointBaseEmbedding 6) := by
  have ht : ∀ Q : Finset (Fin 6),
      seed5ExtraLeftSigns (Q.image (Fin.castSuccOrderEmb : Fin 6 ↪o Fin 7)) =
        seed5ExtraBaseSigns Q := by
    decide
  exact fromOrderedSigns_preserves
    (g := (Fin.castSuccOrderEmb : Fin 6 ↪o Fin 7))
    seed5ExtraBaseSigns seed5ExtraLeftSigns ht

theorem seed5Extra_base_right :
    Preserves seed5ExtraBase seed5ExtraRight (onePointBaseEmbedding 6) := by
  have ht : ∀ Q : Finset (Fin 6),
      seed5ExtraRightSigns (Q.image (Fin.castSuccOrderEmb : Fin 6 ↪o Fin 7)) =
        seed5ExtraBaseSigns Q := by
    decide
  exact fromOrderedSigns_preserves
    (g := (Fin.castSuccOrderEmb : Fin 6 ↪o Fin 7))
    seed5ExtraBaseSigns seed5ExtraRightSigns ht

def directAllowed0135 {k : ℕ}
    (signs : Finset (Fin k) → Bool) (Q : Finset (Fin k)) : Prop :=
  Q.card = 6 →
    let c := directFacetPositiveCount signs Q
    min c (6 - c) = 0 ∨ min c (6 - c) = 1 ∨ min c (6 - c) = 3

theorem seed5Extra_base_direct :
    ∀ Q : Finset (Fin 6), directAllowed0135 seed5ExtraBaseSigns Q := by
  unfold directAllowed0135 directFacetPositiveCount
  decide +kernel

theorem seed5Extra_left_direct :
    ∀ Q : Finset (Fin 7), directAllowed0135 seed5ExtraLeftSigns Q := by
  unfold directAllowed0135 directFacetPositiveCount
  decide +kernel

theorem seed5Extra_right_direct :
    ∀ Q : Finset (Fin 7), directAllowed0135 seed5ExtraRightSigns Q := by
  unfold directAllowed0135 directFacetPositiveCount
  decide +kernel

theorem seed5Extra_base_admissible :
    Admissible ({0,1,3} : Set ℕ) seed5ExtraBase := by
  apply fromOrderedSigns_admissible_five_of_direct_count
    seed5ExtraBaseSigns {0,1,3}
  intro Q hQ
  have h := seed5Extra_base_direct Q hQ
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h

theorem seed5Extra_left_admissible :
    Admissible ({0,1,3} : Set ℕ) seed5ExtraLeft := by
  apply fromOrderedSigns_admissible_five_of_direct_count
    seed5ExtraLeftSigns {0,1,3}
  intro Q hQ
  have h := seed5Extra_left_direct Q hQ
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h

theorem seed5Extra_right_admissible :
    Admissible ({0,1,3} : Set ℕ) seed5ExtraRight := by
  apply fromOrderedSigns_admissible_five_of_direct_count
    seed5ExtraRightSigns {0,1,3}
  intro Q hQ
  have h := seed5Extra_right_direct Q hQ
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h

end Hypertournaments
