import Hypertournaments.FinitePresentation
import Hypertournaments.Obstruction

/-!
# Arity-four central-only one-point witness: exact source tables

The common seven-vertex base and the two one-point extensions are
taken literally from the technical note (Lemma 4-central).

We present the left new point as vertex 7, rather than as a new
first point ℓ, so old vertices have the same canonical embedding
in both sides. Moving ℓ across three old vertices changes the
orientation sign; hence the left link is the *complement* of alpha.

The tables are finite data. The formal goal is to prove admissibility,
agreement on the base, and then the mixed-packet contradiction.
-/

namespace Hypertournaments

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- Seven positive base four-sets, on old vertices 0..6. -/
def seed4OldPlus7 : Finset (Finset (Fin 7)) :=
  { {0,1,2,3}, {0,1,2,5}, {0,2,3,4}, {0,2,3,6},
    {0,2,5,6}, {1,2,3,5}, {1,2,4,5} }

/-- The same old positive four-sets, now within Fin 8. -/
def seed4OldPlus8 : Finset (Finset (Fin 8)) :=
  { {0,1,2,3}, {0,1,2,5}, {0,2,3,4}, {0,2,3,6},
    {0,2,5,6}, {1,2,3,5}, {1,2,4,5} }

/-- Positive left link alpha(i,j,k), with ℓ first. -/
def seed4AlphaPlus8 : Finset (Finset (Fin 8)) :=
  { {0,1,3}, {0,1,4}, {0,1,5}, {0,1,6},
    {0,2,4}, {0,2,5}, {0,2,6}, {0,3,5},
    {0,4,5}, {0,4,6}, {0,5,6}, {1,5,6},
    {2,4,5}, {2,5,6}, {3,5,6}, {4,5,6} }

/-- Positive right link beta(i,j,k), with r last. -/
def seed4BetaPlus8 : Finset (Finset (Fin 8)) :=
  { {0,1,4}, {0,1,5}, {0,1,6}, {0,2,5},
    {0,4,6}, {0,5,6}, {1,4,6}, {1,5,6},
    {2,4,6}, {2,5,6}, {3,4,6}, {3,5,6},
    {4,5,6} }

/-- Sign table of the common base. -/
def seed4BaseSigns (Q : Finset (Fin 7)) : Bool :=
  decide (Q ∈ seed4OldPlus7)

/-- Left side: the new point 7 has the opposite sign to
alpha when 7 is placed last in the canonical presentation. -/
def seed4LeftSigns (Q : Finset (Fin 8)) : Bool :=
  if (7 : Fin 8) ∈ Q then
    !(decide (Q.erase 7 ∈ seed4AlphaPlus8))
  else
    decide (Q ∈ seed4OldPlus8)

/-- Right side: the new point 7 represents r and is already last. -/
def seed4RightSigns (Q : Finset (Fin 8)) : Bool :=
  if (7 : Fin 8) ∈ Q then
    decide (Q.erase 7 ∈ seed4BetaPlus8)
  else
    decide (Q ∈ seed4OldPlus8)

def seed4Base : Hyper 4 (Fin 7) :=
  Hyper.fromOrderedSigns seed4BaseSigns

def seed4Left : Hyper 4 (Fin 8) :=
  Hyper.fromOrderedSigns seed4LeftSigns

def seed4Right : Hyper 4 (Fin 8) :=
  Hyper.fromOrderedSigns seed4RightSigns

/-- The two sign tables restrict to the same seven-vertex base.
Only 128 possible subsets of Fin 7 are checked, not every
injection of a four-tuple. -/
theorem seed4_base_left : Preserves seed4Base seed4Left
    (onePointBaseEmbedding 7) := by
  have htable : ∀ Q : Finset (Fin 7),
      seed4LeftSigns (Q.image (Fin.castSuccOrderEmb : Fin 7 ↪o Fin 8)) =
        seed4BaseSigns Q := by
    decide
  exact fromOrderedSigns_preserves
    (g := (Fin.castSuccOrderEmb : Fin 7 ↪o Fin 8))
    seed4BaseSigns seed4LeftSigns htable

theorem seed4_base_right : Preserves seed4Base seed4Right
    (onePointBaseEmbedding 7) := by
  have htable : ∀ Q : Finset (Fin 7),
      seed4RightSigns (Q.image (Fin.castSuccOrderEmb : Fin 7 ↪o Fin 8)) =
        seed4BaseSigns Q := by
    decide
  exact fromOrderedSigns_preserves
    (g := (Fin.castSuccOrderEmb : Fin 7 ↪o Fin 8))
    seed4BaseSigns seed4RightSigns htable

end Hypertournaments
