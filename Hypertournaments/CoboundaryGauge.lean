import Mathlib.Tactic.Abel
import Hypertournaments.Cochain

/-!
# Gauge normal form for all parity-respecting mixed completions

On the full finite simplex, the unsigned F₂ coboundary is exact in
every positive degree by the already proved explicit cone contraction.
If two cochains have the same coboundary on all (r+1)-sets, then
their difference is closed there, so one cochain differs from the
other by an exact coboundary on all r-sets.

This is the precise mathematical gauge-fixing principle needed
in the odd p3 exceptional non-amalgamation argument: every mixed
completion satisfying the parity constraints has the form
x = h + δu; it is *not* a restriction to a preferred completion.
-/

namespace Hypertournaments

theorem coboundary_equal_on_degree_implies_gauge
    {V : Type*} [DecidableEq V]
    (a : V) (r : ℕ)
    (x h : Finset V → ZMod 2)
    (heq : ∀ Q : Finset V, Q.card = r+1 →
      coboundary x Q = coboundary h Q) :
    ∃ u : Finset V → ZMod 2,
      ∀ Q : Finset V, Q.card = r →
        x Q = h Q + coboundary u Q := by
  let g : Finset V → ZMod 2 := fun Q => x Q - h Q
  have hclosed : ∀ Q : Finset V, Q.card = r+1 →
      coboundary g Q = 0 := by
    intro Q hQ
    calc
      coboundary g Q = coboundary x Q - coboundary h Q := by
        simp [coboundary, g, Finset.sum_sub_distrib]
      _ = 0 := by rw [heq Q hQ]; exact sub_self _
  refine ⟨contractAt a g, ?_⟩
  intro Q hQ
  have hcone := cocycle_exact_at_card a r g hclosed Q hQ
  change coboundary (contractAt a g) Q = x Q - h Q at hcone
  rw [hcone]
  abel

end Hypertournaments
