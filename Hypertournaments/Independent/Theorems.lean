import Hypertournaments.Independent.LinkBridge
import Hypertournaments.Independent.PotentialBridge
import Hypertournaments.Independent.EPPABridge

/-!
# The three independently authored introduction targets

`Statements` retains the independent definitions and targets, with only the
recorded specific-import substitution. The three bridge modules prove exactly
those targets using the original project results and explicit carrier-preserving
representation equivalences.
-/

namespace IndependentHypertournaments

/-- All three independent introduction targets, with no extra hypotheses. -/
theorem all_intro_statements :
    IntroLinkStatement ∧ IntroPotentialStatement ∧ IntroEPPAStatement :=
  ⟨intro_link, potential, intro_eppa⟩

end IndependentHypertournaments
