import Hypertournaments.TwoPadProfileChoice
import Hypertournaments.TwoPadMixedSlice
import Hypertournaments.OnePointJoint

/-!
# Assemble uniform two-pad reflection from genuine profiles

The uniform one-pad pigeonhole argument selects two pads whose actual
raw first two facets agree on EVERY old (n+1)-tuple. Consequently the
recovered intrinsic two-pad slice is admissible without an additional
mixed/nonmixed case distinction.

We provide a reusable theorem returning that admissible slice, then
a one-point-joint reflection interface: whenever the lifted diagram
recovers both lower source orientations for every pair of pads, a
hypothetical higher-arity joint supplies an ordinary lower-arity
amalgam. The source-recovery requirement is stated explicitly rather
than smuggled in as an unproved theorem.

This is not yet the even/odd suspension construction, nor a claim of
unconditional higher-arity negative classification.
-/

namespace Hypertournaments

/-- Pigeonhole on all ordered old facet profiles produces an intrinsic
lower-arity slice whose full age is admissible in the shifted class. -/
theorem exists_admissible_twoPadSlice_of_many_pads
    {n m : ℕ} {W V : Type*}
    [Fintype (Fin (n + 1) ↪ W)]
    (D : Hyper (n + 2) V) (g : W ↪ V)
    (pads : Fin m ↪ V)
    (hpad : ∀ z : Fin m, pads z ∉ Set.range g)
    (T S : Set ℕ) (hD : Admissible T D)
    (hshift : shiftedAllowed T ⊆ S)
    (hm : 2 ^ Fintype.card (Fin (n + 1) ↪ W) < m) :
    ∃ (x y : Fin m) (hxy : x < y) (hpq : pads x ≠ pads y),
      Admissible S
        (D.twoPadSlice g (pads x) (pads y)
          (hpad x) (hpad y) hpq) := by
  obtain ⟨x, y, hxy, hraw⟩ :=
    exists_matchingTwoPadFacets D g pads hpad hm
  have hpq : pads x ≠ pads y := by
    intro heq
    exact (ne_of_lt hxy) (pads.injective heq)
  refine ⟨x, y, hxy, hpq, ?_⟩
  apply D.twoPadSlice_admissible_of_raw_equal g (pads x) (pads y)
    (hpad x) (hpad y) hpq T S hD hshift
  intro t
  exact hraw hpq t

/-- The precise recovery obligation for a lifted ordinary one-point
diagram. Its content is geometrical: for each pair of distinct pads,
the restricted higher-arity orientation recovers both original sides. -/
def RecoversOnePointSidesFromPads
    {n a m : ℕ} {V : Type*}
    (D : Hyper (n + 2) V)
    (g : Fin (a + 2) ↪ V)
    (pads : Fin m ↪ V)
    (hpad : ∀ z : Fin m, pads z ∉ Set.range g)
    (L R : Hyper n (Fin (a + 1))) : Prop :=
  (∀ (x y : Fin m) (hxy : x < y)
      (hpq : pads x ≠ pads y) (t : Fin n ↪ Fin (a + 1)),
      D.orient (twoPadSliceTuple g (pads x) (pads y)
        (hpad x) (hpad y) hpq
        (t.trans (leftJointInclusion a))) = L.orient t) ∧
  (∀ (x y : Fin m) (hxy : x < y)
      (hpq : pads x ≠ pads y) (t : Fin n ↪ Fin (a + 1)),
      D.orient (twoPadSliceTuple g (pads x) (pads y)
        (hpad x) (hpad y) hpq
        (t.trans (rightJointInclusion a))) = R.orient t)

/-- Exact one-point-joint reflection: a large disjoint pad pool and
recovery of each lower-arity source side yield a valid ordinary joint
on the canonical old (a+2)-vertex union. -/
theorem exists_lower_onePoint_joint_of_many_pads
    {n a m : ℕ} {V : Type*}
    (D : Hyper (n + 2) V)
    (g : Fin (a + 2) ↪ V)
    (pads : Fin m ↪ V)
    (hpad : ∀ z : Fin m, pads z ∉ Set.range g)
    (T S : Set ℕ) (hD : Admissible T D)
    (hshift : shiftedAllowed T ⊆ S)
    (hm : 2 ^ Fintype.card (Fin (n + 1) ↪ Fin (a + 2)) < m)
    (L R : Hyper n (Fin (a + 1)))
    (hrecover : RecoversOnePointSidesFromPads D g pads hpad L R) :
    ∃ E : Hyper n (Fin (a + 2)),
      Admissible S E ∧
      Preserves L E (leftJointInclusion a) ∧
      Preserves R E (rightJointInclusion a) := by
  obtain ⟨x, y, hxy, hpq, hslice⟩ :=
    exists_admissible_twoPadSlice_of_many_pads
      D g pads hpad T S hD hshift hm
  let E : Hyper n (Fin (a + 2)) :=
    D.twoPadSlice g (pads x) (pads y) (hpad x) (hpad y) hpq
  refine ⟨E, hslice, ?_, ?_⟩
  · exact Hyper.twoPadSlice_preserves_of_recovery
      L D g (pads x) (pads y) (hpad x) (hpad y) hpq
      (leftJointInclusion a) (hrecover.1 x y hxy hpq)
  · exact Hyper.twoPadSlice_preserves_of_recovery
      R D g (pads x) (pads y) (hpad x) (hpad y) hpq
      (rightJointInclusion a) (hrecover.2 x y hxy hpq)

/-- A previously established lower-arity one-point obstruction
excludes any higher-arity joint satisfying the explicit two-pad
source-recovery conditions and the shifted admissibility inclusion. -/
theorem no_higher_joint_of_many_pads_and_recovery
    {n a m : ℕ} {V : Type*}
    (S T : Set ℕ)
    (L R : Hyper n (Fin (a + 1)))
    (hNoLowJoint : ∀ E : Hyper n (Fin (a + 2)),
      Admissible S E →
      Preserves L E (leftJointInclusion a) →
      Preserves R E (rightJointInclusion a) → False)
    (D : Hyper (n + 2) V)
    (g : Fin (a + 2) ↪ V)
    (pads : Fin m ↪ V)
    (hpad : ∀ z : Fin m, pads z ∉ Set.range g)
    (hD : Admissible T D)
    (hshift : shiftedAllowed T ⊆ S)
    (hm : 2 ^ Fintype.card (Fin (n + 1) ↪ Fin (a + 2)) < m)
    (hrecover : RecoversOnePointSidesFromPads D g pads hpad L R) :
    False := by
  obtain ⟨E, hE, hL, hR⟩ :=
    exists_lower_onePoint_joint_of_many_pads
      D g pads hpad T S hD hshift hm L R hrecover
  exact hNoLowJoint E hE hL hR

end Hypertournaments
