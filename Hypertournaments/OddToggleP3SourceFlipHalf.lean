import Mathlib.SetTheory.Cardinal.Finite
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Hypertournaments.OddToggleP3UniformSourceCounting

/-!
# Exact half-event counting by flipping one independent source bit

The final p3 obstruction must rule out identifying the two fresh
points. For a fixed transversal, disagreement of their old-side
links is an F₂ parity of independent link-source bits and is
unaffected by the base W bit. Flipping any one independent link
bit therefore exchanges agreement and disagreement.

We formalize the underlying exact FINITE principle: if a Boolean
event changes truth value whenever one distinguished source bit
is toggled, then exactly half of all source assignments satisfy it.
A useful corollary handles a parity event
  chosenBit XOR R(otherBits),
where R is invariant under toggling chosenBit.

The actual p3 alpha/beta source representation and choice of
a concrete link bit are still separate proof obligations.
-/

namespace Hypertournaments

/-- Flip exactly one selected Boolean source coordinate. -/
def p3FlipSelectedBit {B : Type*} [DecidableEq B]
    (chosen : B) (values : B → Bool) : B → Bool :=
  fun b => if b = chosen then !(values b) else values b

theorem p3FlipSelectedBit_involutive
    {B : Type*} [DecidableEq B] (chosen : B) :
    Function.Involutive (p3FlipSelectedBit chosen) := by
  intro values
  funext b
  by_cases h : b = chosen <;> simp [p3FlipSelectedBit, h]

/-- Every finite type splits into its event and complement. -/
noncomputable def p3FiniteEventPartitionEquiv
    {Ω : Type*} (P : Ω → Prop) :
    Ω ≃ ({x : Ω // P x} ⊕ {x : Ω // ¬ P x}) := by
  classical
  refine
    { toFun := fun x =>
        if h : P x then Sum.inl ⟨x,h⟩ else Sum.inr ⟨x,h⟩
      invFun := fun z => match z with
        | Sum.inl x => x.val
        | Sum.inr x => x.val
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    by_cases h : P x <;> simp [h]
  · intro z
    rcases z with ⟨x,hx⟩ | ⟨x,hx⟩
    · simp [hx]
    · simp [hx]

/-- Toggling an event-complementing source bit is an equivalence
between event-holding and event-failing global assignments. -/
noncomputable def p3FlippedEventEquiv
    {B : Type*} [DecidableEq B]
    (chosen : B) (P : (B → Bool) → Prop)
    (hflip : ∀ v : B → Bool,
      P (p3FlipSelectedBit chosen v) ↔ ¬P v) :
    {v : B → Bool // P v} ≃
    {v : B → Bool // ¬ P v} where
  toFun v :=
    ⟨p3FlipSelectedBit chosen v.1,
      by
        intro hh
        exact ((hflip v.1).mp hh) v.2⟩
  invFun v :=
    ⟨p3FlipSelectedBit chosen v.1, (hflip v.1).mpr v.2⟩
  left_inv := by
    intro v
    apply Subtype.ext
    exact p3FlipSelectedBit_involutive chosen v.1
  right_inv := by
    intro v
    apply Subtype.ext
    exact p3FlipSelectedBit_involutive chosen v.1

/-- Exact half-event cardinality. The event need not be monotone,
local, probabilistically independent, or explicitly represented
as a sum: the one-bit flip hypothesis is sufficient. -/
theorem p3HalfEvent_of_flip
    {B : Type*} [Fintype B] [DecidableEq B]
    (chosen : B) (P : (B → Bool) → Prop)
    (hflip : ∀ v : B → Bool,
      P (p3FlipSelectedBit chosen v) ↔ ¬P v) :
    2 * Nat.card {v : B → Bool // P v} =
      2 ^ (Fintype.card B) := by
  classical
  let Good := {v : B → Bool // P v}
  let Bad := {v : B → Bool // ¬P v}
  have hEq : Fintype.card Good = Fintype.card Bad :=
    Fintype.card_congr (p3FlippedEventEquiv chosen P hflip)
  have hTotal :
      Fintype.card (B → Bool) =
        Fintype.card Good + Fintype.card Bad := by
    calc
      Fintype.card (B → Bool) = Fintype.card (Good ⊕ Bad) :=
        Fintype.card_congr (p3FiniteEventPartitionEquiv P)
      _ = Fintype.card Good + Fintype.card Bad := by simp
  calc
    2 * Nat.card Good = 2 * Fintype.card Good := by
      simp only [Nat.card_eq_fintype_card]
    _ = Fintype.card Good + Fintype.card Bad := by omega
    _ = Fintype.card (B → Bool) := hTotal.symm
    _ = 2 ^ (Fintype.card B) := by simp

/-- XOR of the chosen independent bit with any functional of all
other bits is true exactly half the time, provided that functional
really is invariant under toggling this selected bit. -/
theorem p3HalfXorEvent_of_flipInvariant
    {B : Type*} [Fintype B] [DecidableEq B]
    (chosen : B) (R : (B → Bool) → Bool)
    (hR : ∀ v : B → Bool,
      R (p3FlipSelectedBit chosen v) = R v) :
    2 * Nat.card
      {v : B → Bool // ((v chosen ^^ R v) = true)} =
      2 ^ (Fintype.card B) := by
  apply p3HalfEvent_of_flip chosen
    (fun v : B → Bool => ((v chosen ^^ R v) = true))
  intro v
  have hChosen :
      (p3FlipSelectedBit chosen v) chosen = ! (v chosen) := by
    simp [p3FlipSelectedBit]
  change (((p3FlipSelectedBit chosen v) chosen ^^
        R (p3FlipSelectedBit chosen v)) = true) ↔
      ¬ ((v chosen ^^ R v) = true)
  rw [hChosen, hR v]
  cases hv : v chosen <;> cases hr : R v <;>
    simp [hv, hr]

end Hypertournaments
