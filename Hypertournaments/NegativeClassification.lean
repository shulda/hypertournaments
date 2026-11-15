import Hypertournaments.OddToggleP3AllBadOnePoint

/-!
# Negative classification: public ordinary-amalgamation interface

This module exports the necessary condition from the audited note without
any remaining exceptional-family premise. Allowed indices must be real,
and the central type is assumed explicitly. No finite Ramsey theorem or
positive-amalgamation result is a hypothesis of these declarations.
-/

namespace Hypertournaments

/-- The necessary condition for ordinary AP, uniformly in every arity
at least four. Both odd exceptional witness families are discharged. -/
theorem negative_classification
    (n : ℕ) (hn : 4 ≤ n)
    (S : Set ℕ) (hvalid : ValidTypes n S)
    (hcentral : centralIndex n ∈ S)
    (hAP : HasAP n S) :
    NecessaryAlternatives n S :=
  negative_classification_all_unconditional n hn S hvalid hcentral hAP

/-- If neither positive alternative holds, even ordinary AP fails.
The positive directions themselves are separate formalization tasks. -/
theorem not_hasAP_of_excluded_types
    (n : ℕ) (hn : 4 ≤ n)
    (S : Set ℕ) (hvalid : ValidTypes n S)
    (hcentral : centralIndex n ∈ S)
    (hnext : nextCentralIndex n ∉ S)
    (hnotSwitching : ¬ (Odd n ∧ S = switchingAllowed n)) :
    ¬ HasAP n S := by
  intro hAP
  rcases negative_classification n hn S hvalid hcentral hAP with h | h
  · exact hnext h
  · exact hnotSwitching h

end Hypertournaments
