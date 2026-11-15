import Hypertournaments.Basic

/-!
# Finite Boolean phases and gauge shifts in the p3 obstruction

For a fixed gauge, the random interior vector is translated by a
deterministic Boolean word. Translation by XOR is an involution and
therefore a bijection on the finite space of assignments.

An alternating word of any positive length is determined uniquely by
its first bit; the two alternating phases are different. These are
the finite counting ingredients needed to turn disjoint random sources
into the exact per-transversal obstruction probability 2^(-m).

These lemmas do not establish any probability or amalgamation claim.
-/

namespace Hypertournaments

/-- Translate a Boolean word by a prescribed word using XOR. -/
def p3BoolTranslate {I : Type*}
    (shift word : I → Bool) : I → Bool :=
  fun i => word i ^^ shift i

/-- Every Boolean XOR translation is its own inverse. -/
theorem p3BoolTranslate_involutive {I : Type*}
    (shift : I → Bool) :
    Function.Involutive (p3BoolTranslate shift) := by
  intro word
  funext i
  cases h : shift i <;> cases hw : word i <;>
    simp [p3BoolTranslate, h, hw]

/-- A fixed gauge changes the random bit vector by a bijection. -/
def p3BoolTranslateEquiv {I : Type*}
    (shift : I → Bool) : (I → Bool) ≃ (I → Bool) where
  toFun := p3BoolTranslate shift
  invFun := p3BoolTranslate shift
  left_inv := p3BoolTranslate_involutive shift
  right_inv := p3BoolTranslate_involutive shift

/-- An alternating Boolean word is prescribed by its initial phase. -/
def p3AlternatingWord (m : ℕ) (phase : Bool) : Fin m → Bool :=
  fun i => if i.val % 2 = 0 then phase else !phase

/-- For a nonempty word the two possible alternating phases are
distinct; the initial position recovers the phase. -/
theorem p3AlternatingWord_injective (m : ℕ) (hm : 0 < m) :
    Function.Injective (p3AlternatingWord m) := by
  intro a b hab
  have hzero := congrFun hab (⟨0, hm⟩ : Fin m)
  simpa [p3AlternatingWord] using hzero

/-- Exactly two distinct alternating words exist in every positive
length. This counts the favorable interior patterns before choosing
the independent endpoint potential bit. -/
theorem p3AlternatingWords_card (m : ℕ) (hm : 0 < m) :
    ((Finset.univ : Finset Bool).image (p3AlternatingWord m)).card = 2 := by
  classical
  rw [Finset.card_image_of_injective _ (p3AlternatingWord_injective m hm)]
  decide

end Hypertournaments
