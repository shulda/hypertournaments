import Hypertournaments.EPPATransfer
import Hypertournaments.EPPAConsequences
import Lean.Elab.Tactic.Omega

/-!
# Non-EPPA for even hypertournaments in every odd arity at least five

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`cor:even-no-eppa`. The arity-lowering theorem would give unrestricted
EPPA one arity below, contradicting the proved PC-family obstruction.
-/

namespace Hypertournaments

/-- Every even odd-arity class from arity five onward fails ordinary EPPA. -/
theorem even_not_hasEPPA (n : ℕ) (hn : Odd n) (hn5 : 5 ≤ n) :
    ¬ HasEPPA (localForbiddenFamily n (switchingAllowed n)) := by
  intro h
  have hdown := eppa_one_arity_down n hn (by omega) (Or.inl h)
  exact pair_cancelling_not_EPPA (by omega) (emptyForbiddenFamily (n - 1))
    (emptyForbiddenFamily_pairCancelling (n - 1)) hdown

/-- The new small-arity instance highlighted in the article's introduction. -/
theorem even_five_not_hasEPPA : ¬ HasEPPA (localForbiddenFamily 5 (switchingAllowed 5)) :=
  even_not_hasEPPA 5 (by decide) (by decide)

end Hypertournaments
