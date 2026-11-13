import Hypertournaments.OddToggleP3PotentialPresentation
import Hypertournaments.Cochain

/-!
# Small exact bridges from p3 F₂ cochains to genuine Boolean facets

A mixed p3 facet is represented by a double contraction of the
intrinsic canonical sign cochain. When the two fresh vertices
are distinct and both outside the selected old subset, it equals
the canonical orientation of the literal set with both fresh
vertices added. Moreover, addition of an F₂-valued gauge bit
is precisely XOR of the corresponding Boolean orientation bits.

These simple algebraic identities isolate the final transport
of actual mixed-facet source/gauge formulas to raw packet bits.
-/

namespace Hypertournaments

/-- Converting an original Boolean orientation into ZMod 2 and
back preserves the bit. -/
theorem p3Bool_of_bitToZMod (b : Bool) :
    p3ZMod2ToBool (p1BitToZMod b) = b := by
  cases b <;> decide

/-- The Boolean representation of F₂ addition is XOR. -/
theorem p3Bool_of_ZMod_add (x y : ZMod 2) :
    p3ZMod2ToBool (x+y) =
      (p3ZMod2ToBool x ^^ p3ZMod2ToBool y) := by
  have h : ∀ a b : ZMod 2,
    p3ZMod2ToBool (a+b) =
      (p3ZMod2ToBool a ^^ p3ZMod2ToBool b) := by decide
  exact h x y

/-- Each actual F₂ independent source bit translated by a
fixed lower gauge cochain is exactly a Boolean XOR-shift. -/
theorem p3Bool_of_source_plus_gauge (b : Bool) (u : ZMod 2) :
    p3ZMod2ToBool (p1BitToZMod b + u) =
      b ^^ p3ZMod2ToBool u := by
  rw [p3Bool_of_ZMod_add, p3Bool_of_bitToZMod]

/-- For two distinct points outside an old subset, the nested
contraction is exactly the cochain's value on the literal
mixed finite set containing both new points. -/
theorem p3DoubleContractAt_eq_mixedSet
    {V : Type*} [DecidableEq V]
    (l r : V) (hlr : l ≠ r)
    (g : Finset V → ZMod 2) (S : Finset V)
    (hl : l ∉ S) (hr : r ∉ S) :
    contractAt r (contractAt l g) S =
      g (insert l (insert r S)) := by
  have hlrS : l ∉ insert r S := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hlr, hl⟩
  simp only [contractAt, if_neg hr, if_neg hlrS]

end Hypertournaments
