import Hypertournaments.Basic

/-!
# Exact Boolean base-bit polarity for protected mixed p3 packets

In the exceptional n ≡ 3 (mod 4) random one-point diagram, each
transversal Q has two endpoint signs
  alpha(Q) = W(Q) xor L(Q), beta(Q) = W(Q) xor R(Q),
while its mixed interior word is fixed after choosing the L/R
potentials and the gauge.

When the interior is alternating, parity makes L(Q) and R(Q)
opposite. Then exactly one value of the independent base bit
W(Q) makes the two endpoint bits align with that alternating
interior, completing a forbidden homogeneous packet.

These lemmas certify the finite deterministic polarity fact,
not probabilistic independence or the full p3 obstruction.
-/

namespace Hypertournaments

/-- A common XOR with the base potential does not change whether
the two endpoint contributions are opposite. -/
theorem p3MixedBaseFlip_preserves_endpoint_disagreement
    (w left right : Bool) :
    ((w ^^ left) ≠ (w ^^ right)) ↔ left ≠ right := by
  cases w <;> cases left <;> cases right <;> decide

/-- For a prescribed alternating interior phase b and two
opposite endpoint contributions, exactly one base bit W produces
the homogeneous endpoint pattern beta=not b, alpha=b. -/
theorem p3UniqueBaseBit_for_alternating_endpoints
    (b left right : Bool) (hLR : left ≠ right) :
    ∃! w : Bool, (w ^^ left = b) ∧ (w ^^ right = !b) := by
  cases b <;> cases left <;> cases right
  all_goals
    first
    | exact (by decide)
    | exact False.elim (hLR rfl)

end Hypertournaments
