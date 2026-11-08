import Hypertournaments.OnePointJoint

/-!
# Every nonmixed tuple in a canonical one-point joint lies in a source side

An ordinary amalgam of two distinct one-point extensions over an
a-vertex base can be restricted to the canonical joint Fin (a+2).
The two new vertices have indices a (left) and a+1 (right).

A tuple is mixed exactly when its image contains both these vertices.
If it is not mixed, it factors through the left or right canonical
inclusion. We prove this as an exact embedding factorization, with no
order assumption on the tuple and no arity restriction.

This is the second combinatorial input, alongside mixed packet
reflection, for proving admissibility of the recovered lower-arity
amalgam. It is entirely independent of the higher-arity suspension.
-/

namespace Hypertournaments

/-- An old (n+1)-tuple is mixed when it involves both newly added
points of the canonical union of two one-point extensions. -/
def IsMixedOnePointTuple (n a : ℕ)
    (t : Fin (n + 1) ↪ Fin (a + 2)) : Prop :=
  (Fin.last a).castSucc ∈ Set.range t ∧
  Fin.last (a + 1) ∈ Set.range t

/-- If an old tuple omits the right new vertex, it factors through
the left source inclusion. The inverse is Fin.castPred. -/
theorem onePointTuple_factors_left
    {k a : ℕ} (t : Fin k ↪ Fin (a + 2))
    (hmiss : Fin.last (a + 1) ∉ Set.range t) :
    ∃ f : Fin k ↪ Fin (a + 1),
      f.trans (leftJointInclusion a) = t := by
  have hn (i : Fin k) : t i ≠ Fin.last (a + 1) := by
    intro hi
    exact hmiss ⟨i, hi⟩
  let f : Fin k ↪ Fin (a + 1) :=
    ⟨(fun i => (t i).castPred (hn i)), by
      intro i j hij
      apply t.injective
      calc
        t i = ((t i).castPred (hn i)).castSucc :=
          (Fin.castSucc_castPred (t i) (hn i)).symm
        _ = ((t j).castPred (hn j)).castSucc :=
          congrArg Fin.castSucc hij
        _ = t j := Fin.castSucc_castPred (t j) (hn j)⟩
  refine ⟨f, ?_⟩
  ext i
  exact congrArg Fin.val (Fin.castSucc_castPred (t i) (hn i))

/-- If an old tuple omits the left new vertex, it factors through
the right source inclusion. The inverse is Fin.predAbove. -/
theorem onePointTuple_factors_right
    {k a : ℕ} (t : Fin k ↪ Fin (a + 2))
    (hmiss : (Fin.last a).castSucc ∉ Set.range t) :
    ∃ f : Fin k ↪ Fin (a + 1),
      f.trans (rightJointInclusion a) = t := by
  have hn (i : Fin k) : t i ≠ (Fin.last a).castSucc := by
    intro hi
    exact hmiss ⟨i, hi⟩
  let f : Fin k ↪ Fin (a + 1) :=
    ⟨(fun i => (Fin.last a).predAbove (t i)), by
      intro i j hij
      apply t.injective
      calc
        t i = ((Fin.last a).castSucc).succAbove
          ((Fin.last a).predAbove (t i)) :=
            (Fin.succAbove_predAbove (hn i)).symm
        _ = ((Fin.last a).castSucc).succAbove
          ((Fin.last a).predAbove (t j)) :=
            congrArg ((Fin.last a).castSucc.succAbove) hij
        _ = t j := Fin.succAbove_predAbove (hn j)⟩
  refine ⟨f, ?_⟩
  ext i
  exact congrArg Fin.val (Fin.succAbove_predAbove (hn i))

/-- An arbitrary nonmixed tuple of the canonical (a+2)-vertex
joint factors through at least one of its one-point source sides. -/
theorem onePointTuple_nonmixed_factors
    {n a : ℕ} (t : Fin (n + 1) ↪ Fin (a + 2))
    (hnot : ¬ IsMixedOnePointTuple n a t) :
    (∃ l : Fin (n + 1) ↪ Fin (a + 1),
       l.trans (leftJointInclusion a) = t) ∨
    (∃ r : Fin (n + 1) ↪ Fin (a + 1),
       r.trans (rightJointInclusion a) = t) := by
  unfold IsMixedOnePointTuple at hnot
  by_cases hleft : (Fin.last a).castSucc ∈ Set.range t
  · left
    apply onePointTuple_factors_left t
    intro hright
    exact hnot ⟨hleft, hright⟩
  · right
    exact onePointTuple_factors_right t hleft

end Hypertournaments
