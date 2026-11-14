import Hypertournaments.CentralUnbounded
import Hypertournaments.PositiveClassification

/-!
# Classification of the unbounded locally constrained classes

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`thm:constrained-classification`. The finite Ramsey argument discharges
central membership from actual unboundedness before applying the exact
ordinary-amalgamation criterion.
-/

namespace Hypertournaments

/-- The article's ordinary-AP criterion for unbounded local-index classes. -/
theorem unbounded_amalgamation_classification (n : ℕ) (hn : 4 ≤ n)
    (S : Set ℕ) (hvalid : ValidTypes n S) (hU : UnboundedAdmissible n S) :
    HasAP n S ↔ NecessaryAlternatives n S :=
  amalgamation_classification n hn S hvalid ((unboundedAdmissible_iff_central n S).mp hU)

/-- A single iff describes exactly the valid palettes giving unbounded
ordinary-amalgamation classes. Both sufficiency alternatives are proved. -/
theorem unbounded_amalgamation_iff (n : ℕ) (hn : 4 ≤ n)
    (S : Set ℕ) (hvalid : ValidTypes n S) :
    (UnboundedAdmissible n S ∧ HasAP n S) ↔
      (centralIndex n ∈ S ∧ NecessaryAlternatives n S) := by
  constructor
  · rintro ⟨hU, hAP⟩
    have hcentral := (unboundedAdmissible_iff_central n S).mp hU
    exact ⟨hcentral, negative_classification n hn S hvalid hcentral hAP⟩
  · rintro ⟨hcentral, hAlt⟩
    exact ⟨(unboundedAdmissible_iff_central n S).mpr hcentral,
      positive_classification n hn S hcentral hAlt⟩

end Hypertournaments
