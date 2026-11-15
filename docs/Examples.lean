import Hypertournaments

/-! Small compiled examples used by the researcher Wiki. -/

open Hypertournaments

example {n : ℕ} (hn : 3 ≤ n)
    (family : ForbiddenFamily n)
    (hpc : ∀ m F, F ∈ family m → PairCancelling F) :
    HasStrongAmalgamation family :=
  pair_cancelling_hasStrongAmalgamation hn family hpc

example (n : ℕ) (hn : 4 ≤ n) (S : Set ℕ)
    (hvalid : ValidTypes n S) (hcentral : centralIndex n ∈ S) :
    HasAP n S ↔ NecessaryAlternatives n S :=
  amalgamation_classification n hn S hvalid hcentral

#check Hypertournaments.Hyper.isEven_iff_exists_potential
#check Hypertournaments.Ramsey.pair_cancelling_ordered_ramsey
#check Hypertournaments.Ramsey.pair_cancelling_ordering_property
#check Hypertournaments.strict_constrained_hierarchy
#check Hypertournaments.continuum_homogeneous_hypertournaments
