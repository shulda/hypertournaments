import Hypertournaments.CoboundaryGauge
import Hypertournaments.OddToggleP3CochainSideLinks

/-!
# All parity-respecting mixed completions have a gauge

For an old base vertex set V, let alpha and beta be the two
one-point side orientation links. Suppose their sum agrees with
the boundary of a prescribed side potential h. If the mixed
orientation cochain x satisfies the actual parity packet equations
delta x = alpha+beta, then delta x = delta h.

The contractible finite-simplex cochain theorem yields x=h+delta u
on all mixed (m-1)-sets. Crucially this conclusion applies to
EVERY possible parity-respecting x, not merely a chosen completion.
The eventual intrinsic p3 proof must still establish the two
premises for the concrete one-point hyperturnaments.
-/

namespace Hypertournaments

/-- Every potential mixed completion with side link sum δh and
the mixed parity constraint has the required exact gauge form. -/
theorem p3MixedGauge_of_link_parity
    {V : Type*} [DecidableEq V] (a : V)
    (m : ℕ) (hm : 1 ≤ m)
    (alpha beta h x : Finset V → ZMod 2)
    (hlink : ∀ Q : Finset V, Q.card = m →
      alpha Q + beta Q = coboundary h Q)
    (hmixed : ∀ Q : Finset V, Q.card = m →
      coboundary x Q = alpha Q + beta Q) :
    ∃ u : Finset V → ZMod 2,
      ∀ U : Finset V, U.card = m-1 →
        x U = h U + coboundary u U := by
  refine coboundary_equal_on_degree_implies_gauge a (m-1) x h ?_
  intro Q hQ
  have hcard : Q.card = m := by omega
  exact (hmixed Q hcard).trans (hlink Q hcard)

end Hypertournaments
