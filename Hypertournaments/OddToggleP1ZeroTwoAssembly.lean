import Hypertournaments.OddToggleP1Parity
import Hypertournaments.OddToggleP1ZeroTwoAbstract

/-!
# Exact zero-or-two conclusion from phase geometry and cochain parity

This module assembles the two independent, previously developed
lemmas for the p1 exceptional odd-arity construction:
(1) raw alternating phases make homogeneous deletions inject into Bool;
(2) if their indicators equal an unsigned coboundary on each deleted
parent, double coboundary vanishes and their count is even.

The result is arity-uniform and fully finite. Hypotheses make explicit
what still has to be verified for *actual* constrained hypertournaments:
the raw phase geometry and the identification of the homogeneous
indicator with coboundary parity. It assumes neither AP failure nor
any mysterious combinatorial extension theorem.
-/

namespace Hypertournaments

/-- Abstract full zero-or-two principle, with explicit raw phases
and simplex coboundary representation on the same parent set. -/
theorem p1Cochain_zero_or_two_of_phase
    (n : ℕ)
    (raw : Finset (Fin (n+2)) → Bool)
    (H : Fin (n+2) → Prop) [DecidablePred H]
    (phase : Fin (n+2) → Bool)
    (e : Finset (Fin (n+2)) → ZMod 2)
    (hraw : ∀ i, H i → ∀ j, j ≠ i →
      raw (((Finset.univ : Finset (Fin (n+2))).erase i).erase j) =
        (phase i ^^ decide ((p1ErasePosition i j)%2=1)))
    (hind : ∀ i : Fin (n+2),
      (if H i then (1 : ZMod 2) else 0) =
        coboundary e ((Finset.univ : Finset (Fin (n+2))).erase i)) :
    (Finset.univ.filter H).card = 0 ∨
      (Finset.univ.filter H).card = 2 := by
  have hle : (Finset.univ.filter H).card ≤ 2 :=
    p1RawHomogeneous_card_le_two n raw H phase hraw
  have heven :
      (((Finset.univ : Finset (Fin (n+2))).filter H).card : ZMod 2) = 0 := by
    apply p1Cochain_homogeneous_count_even
      (Finset.univ : Finset (Fin (n+2))) e H
    intro i _
    exact hind i
  exact p1Even_card_le_two_eq_zero_or_two
    (Finset.univ.filter H).card hle heven

end Hypertournaments
