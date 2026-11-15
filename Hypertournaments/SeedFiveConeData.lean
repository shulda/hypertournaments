import Hypertournaments.GeneralDirectPacket
import Hypertournaments.SeedFourData

/-!
# Arity-five central-only cone: explicit finite witness data

We cone the previously kernel-checked central-only four-ary
non-amalgamation span. The new common cone vertex is 0 and every old
vertex is shifted by one. For a five-set with cone vertex, its sign is
the underlying four-ary sign. For a five-set without cone vertex, its
sign is the alternating integer boundary of the four-ary sign table.

The latter boundary is +1 or -1, since every old five-set has
central type 2. A positive boundary means three positive normalized
four-facets; a negative boundary means two. The following
literal supports are generated from that formula and can be audited
independently. All ambient six-sets in the three source structures
have central type 3, checked by the Lean kernel.

This file establishes a genuine admissible one-point span in
arity five. Non-amalgamation (including identification) is not
asserted here; it will be reflected from the arity-four seed.
-/

namespace Hypertournaments

set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

/-- Positive five-facets on the coned eight-vertex common base. -/
def seed5ConeBasePlus : Finset (Finset (Fin 8)) :=
  { {0,1,2,3,4},
    {0,1,2,3,6},
    {0,1,3,4,5},
    {0,1,3,4,7},
    {0,1,3,6,7},
    {0,2,3,4,6},
    {0,2,3,5,6},
    {1,2,3,4,6},
    {1,3,4,5,6},
    {1,3,5,6,7},
    {2,3,4,6,7},
    {2,3,5,6,7} }

/-- Positive five-facets of the coned left one-point extension. -/
def seed5ConeLeftPlus : Finset (Finset (Fin 9)) :=
  { {0,1,2,3,4},
    {0,1,2,3,6},
    {0,1,2,3,8},
    {0,1,3,4,5},
    {0,1,3,4,7},
    {0,1,3,4,8},
    {0,1,3,6,7},
    {0,1,4,5,8},
    {0,1,4,7,8},
    {0,2,3,4,6},
    {0,2,3,4,8},
    {0,2,3,5,6},
    {0,2,3,5,8},
    {0,2,3,6,8},
    {0,2,3,7,8},
    {0,2,4,5,8},
    {0,2,4,6,8},
    {0,2,4,7,8},
    {0,2,5,6,8},
    {0,2,5,7,8},
    {0,3,4,5,8},
    {0,3,4,6,8},
    {0,3,4,7,8},
    {0,3,5,7,8},
    {0,4,5,6,8},
    {0,4,5,7,8},
    {1,2,3,4,6},
    {1,2,3,6,8},
    {1,2,4,6,8},
    {1,2,5,6,8},
    {1,2,5,7,8},
    {1,3,4,5,6},
    {1,3,5,6,7},
    {1,3,5,7,8},
    {1,3,6,7,8},
    {1,4,5,7,8},
    {1,4,6,7,8},
    {2,3,4,6,7},
    {2,3,4,6,8},
    {2,3,5,6,7},
    {3,4,5,6,8},
    {3,5,6,7,8} }

/-- Positive five-facets of the coned right one-point extension. -/
def seed5ConeRightPlus : Finset (Finset (Fin 9)) :=
  { {0,1,2,3,4},
    {0,1,2,3,6},
    {0,1,2,5,8},
    {0,1,2,6,8},
    {0,1,2,7,8},
    {0,1,3,4,5},
    {0,1,3,4,7},
    {0,1,3,6,7},
    {0,1,3,6,8},
    {0,1,5,7,8},
    {0,1,6,7,8},
    {0,2,3,4,6},
    {0,2,3,5,6},
    {0,2,5,7,8},
    {0,2,6,7,8},
    {0,3,5,7,8},
    {0,3,6,7,8},
    {0,4,5,7,8},
    {0,4,6,7,8},
    {0,5,6,7,8},
    {1,2,3,4,6},
    {1,2,3,4,8},
    {1,2,3,5,8},
    {1,2,3,6,8},
    {1,2,3,7,8},
    {1,2,4,5,8},
    {1,2,4,6,8},
    {1,2,4,7,8},
    {1,3,4,5,6},
    {1,3,4,5,8},
    {1,3,4,6,8},
    {1,3,4,7,8},
    {1,3,5,6,7},
    {1,3,5,6,8},
    {1,5,6,7,8},
    {2,3,4,6,7},
    {2,3,4,6,8},
    {2,3,5,6,7},
    {2,3,5,6,8},
    {2,5,6,7,8},
    {3,5,6,7,8},
    {4,5,6,7,8} }

def seed5ConeBaseSigns (Q : Finset (Fin 8)) : Bool :=
  decide (Q ∈ seed5ConeBasePlus)

def seed5ConeLeftSigns (Q : Finset (Fin 9)) : Bool :=
  decide (Q ∈ seed5ConeLeftPlus)

def seed5ConeRightSigns (Q : Finset (Fin 9)) : Bool :=
  decide (Q ∈ seed5ConeRightPlus)

def seed5ConeBase : Hyper 5 (Fin 8) :=
  Hyper.fromOrderedSigns seed5ConeBaseSigns

def seed5ConeLeft : Hyper 5 (Fin 9) :=
  Hyper.fromOrderedSigns seed5ConeLeftSigns

def seed5ConeRight : Hyper 5 (Fin 9) :=
  Hyper.fromOrderedSigns seed5ConeRightSigns

/-- Both source sides agree with the coned common eight-vertex base. -/
theorem seed5Cone_base_left :
    Preserves seed5ConeBase seed5ConeLeft (onePointBaseEmbedding 8) := by
  have ht : ∀ Q : Finset (Fin 8),
      seed5ConeLeftSigns
        (Q.image (Fin.castSuccOrderEmb : Fin 8 ↪o Fin 9)) =
          seed5ConeBaseSigns Q := by decide
  exact fromOrderedSigns_preserves
    (g := (Fin.castSuccOrderEmb : Fin 8 ↪o Fin 9))
    seed5ConeBaseSigns seed5ConeLeftSigns ht

theorem seed5Cone_base_right :
    Preserves seed5ConeBase seed5ConeRight (onePointBaseEmbedding 8) := by
  have ht : ∀ Q : Finset (Fin 8),
      seed5ConeRightSigns
        (Q.image (Fin.castSuccOrderEmb : Fin 8 ↪o Fin 9)) =
          seed5ConeBaseSigns Q := by decide
  exact fromOrderedSigns_preserves
    (g := (Fin.castSuccOrderEmb : Fin 8 ↪o Fin 9))
    seed5ConeBaseSigns seed5ConeRightSigns ht

/-- A finite rank-based centrality test on every canonical six-set. -/
def seed5ConeCentralAt {k : ℕ}
    (signs : Finset (Fin k) → Bool) (Q : Finset (Fin k)) : Prop :=
  Q.card = 6 →
    min (directFacetPositiveCount signs Q)
      (6 - directFacetPositiveCount signs Q) = 3

theorem seed5Cone_base_direct :
    ∀ Q : Finset (Fin 8), seed5ConeCentralAt seed5ConeBaseSigns Q := by
  unfold seed5ConeCentralAt directFacetPositiveCount
  decide +kernel

theorem seed5Cone_left_direct :
    ∀ Q : Finset (Fin 9), seed5ConeCentralAt seed5ConeLeftSigns Q := by
  unfold seed5ConeCentralAt directFacetPositiveCount
  decide +kernel

theorem seed5Cone_right_direct :
    ∀ Q : Finset (Fin 9), seed5ConeCentralAt seed5ConeRightSigns Q := by
  unfold seed5ConeCentralAt directFacetPositiveCount
  decide +kernel

/-- Full intrinsic admissibility of the cone span. -/
theorem seed5Cone_base_admissible :
    Admissible ({3} : Set ℕ) seed5ConeBase := by
  apply fromOrderedSigns_admissible_five_of_direct_count
    seed5ConeBaseSigns {3}
  intro Q hQ
  have h := seed5Cone_base_direct Q hQ
  simpa [Set.mem_singleton_iff] using h

theorem seed5Cone_left_admissible :
    Admissible ({3} : Set ℕ) seed5ConeLeft := by
  apply fromOrderedSigns_admissible_five_of_direct_count
    seed5ConeLeftSigns {3}
  intro Q hQ
  have h := seed5Cone_left_direct Q hQ
  simpa [Set.mem_singleton_iff] using h

theorem seed5Cone_right_admissible :
    Admissible ({3} : Set ℕ) seed5ConeRight := by
  apply fromOrderedSigns_admissible_five_of_direct_count
    seed5ConeRightSigns {3}
  intro Q hQ
  have h := seed5Cone_right_direct Q hQ
  simpa [Set.mem_singleton_iff] using h

/-- The cone-star signs on every four-set reproduce the underlying
four-hypertournament source table (here the canonical shifting map
sends original vertex i to new vertex i+1). -/
theorem seed5Cone_base_star :
    ∀ Q : Finset (Fin 7), Q.card = 4 →
      seed5ConeBaseSigns (insert 0 (Q.image (Fin.succ : Fin 7 → Fin 8))) =
        seed4BaseSigns Q := by
  decide +kernel

theorem seed5Cone_left_star :
    ∀ Q : Finset (Fin 8), Q.card = 4 →
      seed5ConeLeftSigns (insert 0 (Q.image (Fin.succ : Fin 8 → Fin 9))) =
        seed4LeftSigns Q := by
  decide +kernel

theorem seed5Cone_right_star :
    ∀ Q : Finset (Fin 8), Q.card = 4 →
      seed5ConeRightSigns (insert 0 (Q.image (Fin.succ : Fin 8 → Fin 9))) =
        seed4RightSigns Q := by
  decide +kernel

end Hypertournaments
