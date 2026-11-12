import Hypertournaments.Cochain

/-!
# Exact finite number of p3 mixed-gauge choices

The universal mixed-joint gauge has a cochain u of degree m-2 on
the a=mt old vertices. Although the existing cochain formalization
uses functions on *all* finite subsets, the coboundary on an (m-1)-set
only reads u on the (m-2)-subsets. Consequently the relevant gauge
choices are exactly functions from the fixed-cardinality support,
which has size binomial(a,m-2), to the two-element field.

This module makes this reduction and its exact finite cardinality
available to the p3 union-bound proof. No hypothetical-joint event
bound or non-amalgamation statement is asserted here.
-/

namespace Hypertournaments

/-- The degree-d support of an old-base cochain. -/
abbrev p3GaugeDomain (a d : ℕ) :=
  {U : Finset (Fin a) // U.card = d}

/-- The relevant gauge support has exactly binomial(a,d) facets. -/
theorem p3GaugeDomain_card (a d : ℕ) :
    Fintype.card (p3GaugeDomain a d) = a.choose d := by
  classical
  simpa [p3GaugeDomain] using
    (Fintype.card_finset_len (α := Fin a) d)

/-- There are precisely 2^binomial(a,d) Boolean gauge assignments. -/
theorem p3BoolGaugeChoices_card (a d : ℕ) :
    Fintype.card (p3GaugeDomain a d → Bool) =
      2 ^ (a.choose d) := by
  classical
  rw [Fintype.card_fun, p3GaugeDomain_card]
  simp

/-- The actual F₂ gauge cochains have the same exact cardinality. -/
theorem p3ZModGaugeChoices_card (a d : ℕ) :
    Fintype.card (p3GaugeDomain a d → ZMod 2) =
      2 ^ (a.choose d) := by
  classical
  have hz : Fintype.card (ZMod 2) = 2 := by decide
  rw [Fintype.card_fun, p3GaugeDomain_card, hz]

/-- Restrict an arbitrary lower cochain to the only degree used by
the mixed-packet coboundary. -/
def p3GaugeRestrict (a d : ℕ)
    (u : Finset (Fin a) → ZMod 2) :
    p3GaugeDomain a d → ZMod 2 :=
  fun U => u U.val

/-- Extend supported degree-d values to all finite subsets, using
zero outside the actual support. -/
noncomputable def p3GaugeExtend (a d : ℕ)
    (v : p3GaugeDomain a d → ZMod 2) :
    Finset (Fin a) → ZMod 2 := by
  classical
  exact fun U =>
    if h : U.card = d then v ⟨U, h⟩ else 0

/-- The canonical extension realizes every prescribed degree-d
gauge assignment: no hidden compatibility constraints. -/
theorem p3GaugeRestrict_surjective (a d : ℕ) :
    Function.Surjective (p3GaugeRestrict a d) := by
  intro values
  refine ⟨p3GaugeExtend a d values, ?_⟩
  funext U
  simp [p3GaugeRestrict, p3GaugeExtend, U.property]

/-- Normalizing a general cochain off degree d does not alter its
coboundary on any degree-(d+1) packet. Therefore the finitely
many supported gauges above exhaust ALL relevant mixed completions. -/
theorem p3GaugeRestrictExtend_coboundary
    (a d : ℕ) (u : Finset (Fin a) → ZMod 2)
    (Q : Finset (Fin a)) (hQ : Q.card = d+1) :
    coboundary (p3GaugeExtend a d (p3GaugeRestrict a d u)) Q =
      coboundary u Q := by
  classical
  unfold coboundary
  apply Finset.sum_congr rfl
  intro x hx
  have hsize : (Q.erase x).card = d := by
    have hh := Finset.card_erase_of_mem hx
    omega
  simp [p3GaugeExtend, p3GaugeRestrict, hsize]

end Hypertournaments
