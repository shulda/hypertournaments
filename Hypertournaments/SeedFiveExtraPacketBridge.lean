import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Hypertournaments.SeedFiveExtraBoolean
import Hypertournaments.OnePointJoint

/-!
# Semantic bridge for the exceptional five-ary {0,1,3} class

A six-facet packet with fixed endpoint orientation bits beta, alpha
has normalized signs (beta, !d, c, !b, a, !alpha).
The complete admissibility criterion for local indices 0,1,3 is
even XOR parity of a,b,c,d when beta=alpha, and odd XOR parity
plus one homogeneous exceptional assignment otherwise.

We prove this from actual intrinsic localIndex and not merely a
syntactic Boolean overapproximation.
-/

namespace Hypertournaments

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Which Boolean rule the two outer fixed facets select. -/
def seed5ExtraMixedRule (beta alpha a b c d : Bool) : Prop :=
  if beta = alpha then seed5ExtraRuleSame a b c d
  else if beta = false then seed5ExtraRuleZeroOne a b c d
  else seed5ExtraRuleOneZero a b c d

/-- Positive normalized facet count of the six-bit packet. -/
def seed5ExtraMixedPositiveCount (beta alpha a b c d : Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin 6 =>
    (![beta, !d, c, !b, a, !alpha] : Fin 6 → Bool) i = true)).card

/-- Certified finite-set cardinality as an explicit sum of Boolean indicators. -/
theorem seed5ExtraMixedPositiveCount_eq_sum
    (beta alpha a b c d : Bool) :
    seed5ExtraMixedPositiveCount beta alpha a b c d =
      (if beta then 1 else 0) +
      (if !d then 1 else 0) +
      (if c then 1 else 0) +
      (if !b then 1 else 0) +
      (if a then 1 else 0) +
      (if !alpha then 1 else 0) := by
  cases beta <;> cases alpha <;> cases a <;> cases b <;>
    cases c <;> cases d <;> decide +kernel

/-- Exactly the allowed local types yield the XOR/homogeneous rule. -/
theorem seed5ExtraMixedAllowed_iff_rule
    (beta alpha a b c d : Bool) :
    (min (seed5ExtraMixedPositiveCount beta alpha a b c d)
         (6 - seed5ExtraMixedPositiveCount beta alpha a b c d) = 0 ∨
      min (seed5ExtraMixedPositiveCount beta alpha a b c d)
         (6 - seed5ExtraMixedPositiveCount beta alpha a b c d) = 1 ∨
      min (seed5ExtraMixedPositiveCount beta alpha a b c d)
         (6 - seed5ExtraMixedPositiveCount beta alpha a b c d) = 3) ↔
      seed5ExtraMixedRule beta alpha a b c d := by
  simp only [seed5ExtraMixedPositiveCount_eq_sum]
  unfold seed5ExtraMixedRule seed5ExtraRuleSame seed5ExtraRuleZeroOne
    seed5ExtraRuleOneZero
  cases beta <;> cases alpha <;> cases a <;> cases b <;>
    cases c <;> cases d <;> norm_num

/-- Every actual admissible mixed six-tuple satisfies its
selected packet rule. -/
theorem seed5ExtraMixedRule_of_admissible
    {V : Type*} (E : Hyper 5 V) (t : Fin 6 ↪ V)
    (beta alpha a b c d : Bool)
    (h0 : E.orient (facet t 0) = beta)
    (h1 : E.orient (facet t 1) = d)
    (h2 : E.orient (facet t 2) = c)
    (h3 : E.orient (facet t 3) = b)
    (h4 : E.orient (facet t 4) = a)
    (h5 : E.orient (facet t 5) = alpha)
    (hallowed : localIndex E t ∈ ({0,1,3} : Set ℕ)) :
    seed5ExtraMixedRule beta alpha a b c d := by
  have hfacet (i : Fin 6) :
      normalizedFacet E t i =
        (![beta, !d, c, !b, a, !alpha] : Fin 6 → Bool) i := by
    fin_cases i <;> simp [normalizedFacet, h0, h1, h2, h3, h4, h5]
  have hcount :
      positiveFacetCount E t =
        seed5ExtraMixedPositiveCount beta alpha a b c d := by
    unfold positiveFacetCount seed5ExtraMixedPositiveCount
    apply congrArg Finset.card
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hfacet i]
  have hallowed' :
      min (seed5ExtraMixedPositiveCount beta alpha a b c d)
          (6 - seed5ExtraMixedPositiveCount beta alpha a b c d) = 0 ∨
      min (seed5ExtraMixedPositiveCount beta alpha a b c d)
          (6 - seed5ExtraMixedPositiveCount beta alpha a b c d) = 1 ∨
      min (seed5ExtraMixedPositiveCount beta alpha a b c d)
          (6 - seed5ExtraMixedPositiveCount beta alpha a b c d) = 3 := by
    simpa [localIndex, hcount, Set.mem_insert_iff, Set.mem_singleton_iff]
      using hallowed
  exact (seed5ExtraMixedAllowed_iff_rule beta alpha a b c d).mp hallowed'

end Hypertournaments
