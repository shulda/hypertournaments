import Hypertournaments.Identification

/-!
# The Boolean implication core of the arity-four central-only obstruction

This is the hand-checkable seven-triple contradiction from the
AI technical note. The two local packet rules are stated explicitly
and the contradiction is proved by two direct implication chains.

Important scope: this module proves the Boolean contradiction.
Encoding the concrete 7-vertex base, both one-point extensions,
their admissibility, and the bridge from local packet constraints to
these seven rules are separate proof obligations.
-/

namespace Hypertournaments

/-- On a mixed five-set with both endpoint signs negative,
centrality imposes two implications and an incompatibility. -/
def negativePacketRule (a b c : Bool) : Prop :=
  (a = true → b = true) ∧
  (c = true → b = true) ∧
  ¬ (a = true ∧ c = true)

/-- On a mixed five-set with both endpoint signs positive,
centrality imposes two reverse implications and a disjunction. -/
def positivePacketRule (a b c : Bool) : Prop :=
  (b = true → a = true) ∧
  (b = true → c = true) ∧
  (a = true ∨ c = true)

/-- These seven local constraints have no simultaneous solution.
The subscripts are the pairs from the arity-four central-only
one-point witness (base vertices 0 through 6). -/
theorem arityFour_central_seed_rules_unsatisfiable
    (x01 x02 x03 x04 x06 x12 x14 x15 x23 x36 x45 x46 x56 : Bool)
    (h012 : negativePacketRule x01 x02 x12)
    (h014 : positivePacketRule x01 x04 x14)
    (h023 : negativePacketRule x02 x03 x23)
    (h036 : negativePacketRule x03 x06 x36)
    (h046 : positivePacketRule x04 x06 x46)
    (h145 : negativePacketRule x14 x15 x45)
    (h456 : positivePacketRule x45 x46 x56) : False := by
  by_cases h01 : x01 = true
  · have h02 : x02 = true := h012.1 h01
    have h03 : x03 = true := h023.1 h02
    have h06 : x06 = true := h036.1 h03
    have h04 : x04 = true := h046.1 h06
    have h46 : x46 = true := h046.2.1 h06
    have h14 : x14 = true := h014.2.1 h04
    have h45 : x45 = true := h456.1 h46
    exact h145.2.2 ⟨h14, h45⟩
  · have h14 : x14 = true := h014.2.2.resolve_left h01
    have h04 : x04 ≠ true := by
      intro h04
      exact h01 (h014.1 h04)
    have h46 : x46 = true := h046.2.2.resolve_left h04
    have h45 : x45 = true := h456.1 h46
    exact h145.2.2 ⟨h14, h45⟩

end Hypertournaments
