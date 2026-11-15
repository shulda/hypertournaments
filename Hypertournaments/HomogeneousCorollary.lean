import Hypertournaments.Antichain.Construction
import Hypertournaments.ContinuumHomogeneous

/-!
# Continuum many homogeneous hypertournaments with Ramsey ages

Source: `tex_hypertournaments`, commit
`291c032ddbb7029914acc7585d5eb4ec8335dcad`, `cor:sullivan-ramsey`.
The concrete cycle antichain discharges the only input to the abstract
construction. Every member is countably infinite and homogeneous, and every
assertion about its age concerns the actual constructed structure.
-/

namespace Hypertournaments

/-- An explicit family indexed by all subsets of the natural numbers. In
addition to the article's assertions, every age has no finite forbidden basis. -/
noncomputable def continuumHomogeneousFamily (n : ℕ) (hn : 3 ≤ n) :
    ContinuumHomogeneousFamily n :=
  ContinuumHomogeneousFamily.ofAntichain hn (Antichain.cycleIndexedPCAntichain n hn)

/-- For every arity at least three, continuum many pairwise nonisomorphic
countably infinite homogeneous hypertournaments have freely ordered Ramsey
ages with the ordering property. Countability, infinitude and homogeneity
are fields of `CountableHomogeneousHyper`, rather than additional premises. -/
theorem continuum_homogeneous_hypertournaments (n : ℕ) (hn : 3 ≤ n) :
    ∃ M : Set ℕ → CountableHomogeneousHyper n,
      (∀ S T, S ≠ T → ¬ (M S).hyper.Isomorphic (M T).hyper) ∧
      (∀ S, CCO.UnaryHN.Native.Ramsey.{0,0,0} (M S).hyper.orderedAge) ∧
      (∀ S, (M S).hyper.AgeHasOrderingProperty) ∧
      Cardinal.mk (Set.range (fun S => (M S).hyper.finiteAge)) = Cardinal.continuum := by
  let F := continuumHomogeneousFamily n hn
  exact ⟨F.model, F.nonisomorphic, F.ramsey, F.ordering, F.continuum_many_ages⟩

end Hypertournaments
