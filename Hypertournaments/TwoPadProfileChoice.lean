import Mathlib.Tactic.Ext
import Hypertournaments.TwoPadMixedSlice
import Hypertournaments.TwoPadProfiles

/-!
# Pigeonhole matching of actual one-pad orientations

The two-coordinate reflection can use a larger finite auxiliary pad
set than the sharp bound in the handwritten proof.  By recording the
raw orientation of EVERY ordered old (n+1)-tuple with one initial pad,
we obtain two pads whose raw profiles agree on all tuples at once.
This is stronger than the mixed-only matching needed for the source
one-point obstruction and avoids a separate rank/order argument.

Unlike an abstract Boolean pigeonhole step, the theorem here
constructs the actual arity-(n+2) one-pad embeddings, proves their
identity with the two deleted facets of a two-pad tuple, and produces
the exact raw-equality hypothesis required by TwoPadIndexShift.

There is no assumption of an ambient linear order or of strong AP.
-/

namespace Hypertournaments

/-- Prepend one fixed padding vertex to an arbitrary injective old
(n+1)-tuple, after mapping old vertices to the ambient set. -/
def onePadSliceTuple
    {n : ℕ} {W V : Type*}
    (g : W ↪ V) (p : V) (hp : p ∉ Set.range g)
    (t : Fin (n + 1) ↪ W) : Fin (n + 2) ↪ V :=
  Fin.Embedding.cons (t.trans g)
    (not_mem_range_restricted g t p hp)

/-- Deleting the initial pad of a two-pad tuple produces exactly the
one-pad tuple with the second pad. -/
theorem facet_twoPadSliceTuple_zero
    {n : ℕ} {W V : Type*}
    (g : W ↪ V) (p q : V)
    (hp : p ∉ Set.range g) (hq : q ∉ Set.range g)
    (hpq : p ≠ q) (t : Fin (n + 1) ↪ W) :
    facet (twoPadSliceTuple g p q hp hq hpq t) 0 =
      onePadSliceTuple g q hq t := by
  ext k
  refine Fin.cases ?_ (fun i => ?_) k
  · rfl
  · rfl

/-- Deleting the second pad produces exactly the one-pad tuple with
the first pad, with the remaining old coordinates unchanged. -/
theorem facet_twoPadSliceTuple_one
    {n : ℕ} {W V : Type*}
    (g : W ↪ V) (p q : V)
    (hp : p ∉ Set.range g) (hq : q ∉ Set.range g)
    (hpq : p ≠ q) (t : Fin (n + 1) ↪ W) :
    facet (twoPadSliceTuple g p q hp hq hpq t) 1 =
      onePadSliceTuple g p hp t := by
  ext k
  refine Fin.cases ?_ (fun i => ?_) k
  · simp [facet, twoPadSliceTuple, onePadSliceTuple, Fin.one_succAbove_zero]
  · simp [facet, twoPadSliceTuple, onePadSliceTuple, Fin.one_succAbove_succ]

/-- If there are more pad vertices than Boolean profiles indexed by
all ordered old (n+1)-tuples, two ordered pads have identical actual
one-pad orientation profiles. -/
theorem exists_matchingOnePadProfiles
    {n m : ℕ} {W V : Type*}
    [Fintype (Fin (n + 1) ↪ W)]
    (D : Hyper (n + 2) V) (g : W ↪ V)
    (pads : Fin m ↪ V)
    (hpad : ∀ z : Fin m, pads z ∉ Set.range g)
    (hm : 2 ^ Fintype.card (Fin (n + 1) ↪ W) < m) :
    ∃ x y : Fin m, x < y ∧
      ∀ t : Fin (n + 1) ↪ W,
        D.orient (onePadSliceTuple g (pads x) (hpad x) t) =
        D.orient (onePadSliceTuple g (pads y) (hpad y) t) := by
  classical
  obtain ⟨x, y, hxy, hprofile⟩ :=
    repeatedBoolProfile m hm
      (fun z (t : Fin (n + 1) ↪ W) =>
        D.orient (onePadSliceTuple g (pads z) (hpad z) t))
  refine ⟨x, y, hxy, ?_⟩
  intro t
  exact congrFun hprofile t

/-- The matching two-pad profile is precisely equality of the two
raw facets which would otherwise produce a local-type defect. -/
theorem exists_matchingTwoPadFacets
    {n m : ℕ} {W V : Type*}
    [Fintype (Fin (n + 1) ↪ W)]
    (D : Hyper (n + 2) V) (g : W ↪ V)
    (pads : Fin m ↪ V)
    (hpad : ∀ z : Fin m, pads z ∉ Set.range g)
    (hm : 2 ^ Fintype.card (Fin (n + 1) ↪ W) < m) :
    ∃ x y : Fin m, x < y ∧
      ∀ (hpq : pads x ≠ pads y) (t : Fin (n + 1) ↪ W),
        D.orient (facet
          (twoPadSliceTuple g (pads x) (pads y)
            (hpad x) (hpad y) hpq t) 0) =
        D.orient (facet
          (twoPadSliceTuple g (pads x) (pads y)
            (hpad x) (hpad y) hpq t) 1) := by
  obtain ⟨x, y, hxy, hprofile⟩ :=
    exists_matchingOnePadProfiles D g pads hpad hm
  refine ⟨x, y, hxy, ?_⟩
  intro hpq t
  rw [facet_twoPadSliceTuple_zero, facet_twoPadSliceTuple_one]
  exact (hprofile t).symm

end Hypertournaments
