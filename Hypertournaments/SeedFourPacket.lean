import Hypertournaments.SeedFourLogic

/-!
# Exact packet-to-implication conversion for the arity-four seed

The five normalized facet signs for an ordered mixed packet
(l,i,j,k,r) are (beta, -xjk, xik, -xij, alpha).
The raw orientation sign + is encoded by Bool.true.
-/

namespace Hypertournaments

/-- Number of positive signs in a mixed five-facet packet. -/
def mixedPacketPositiveCount4
    (alpha beta xij xik xjk : Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin 5 =>
    (if i.val = 0 then beta
     else if i.val = 1 then !xjk
     else if i.val = 2 then xik
     else if i.val = 3 then !xij
     else alpha) = true)).card

/-- Centrality means exactly two or three positive signs. -/
def mixedPacketCentral4
    (alpha beta xij xik xjk : Bool) : Prop :=
  mixedPacketPositiveCount4 alpha beta xij xik xjk = 2 ∨
  mixedPacketPositiveCount4 alpha beta xij xik xjk = 3

/-- Both endpoint signs negative gives the negative packet rule. -/
theorem mixedPacket_negative_rule_iff
    (xij xik xjk : Bool) :
    mixedPacketCentral4 false false xij xik xjk ↔
      negativePacketRule xij xik xjk := by
  cases xij <;> cases xik <;> cases xjk <;>
    (unfold mixedPacketCentral4 mixedPacketPositiveCount4 negativePacketRule
     decide)

/-- Both endpoint signs positive gives the positive packet rule. -/
theorem mixedPacket_positive_rule_iff
    (xij xik xjk : Bool) :
    mixedPacketCentral4 true true xij xik xjk ↔
      positivePacketRule xij xik xjk := by
  cases xij <;> cases xik <;> cases xjk <;>
    (unfold mixedPacketCentral4 mixedPacketPositiveCount4 positivePacketRule
     decide)

end Hypertournaments
