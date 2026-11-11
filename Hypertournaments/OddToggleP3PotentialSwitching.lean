import Hypertournaments.OddToggleP3PotentialPresentation
import Hypertournaments.OddToggleP3AgeSplit

/-!
# Intrinsic F₂ potential constructions satisfy p3 switching parity

Every potential-induced actual hypertournament has vanishing
canonical cochain coboundary on every increasing packet. The
kernel-proved p3 parity equivalence therefore places it in
switchingAllowed in all arities n=4k+3.

For the exceptional forbidden-homogeneous toggleZero family,
the ONLY additional pointwise requirement is localIndex != 0.
This reduces the age proof for random p3 sides to their protected
zero-facet support geometry, with no separate parity case split.
-/

namespace Hypertournaments

/-- Every finite intrinsic hypertournament obtained from an
arbitrary F₂ potential belongs locally to the p3 switching class. -/
theorem p3HyperFromPotential_switchingAllowed
    (k a : ℕ) (z : Finset (Fin a) → ZMod 2)
    (f : Fin (4*k+4) ↪o Fin a) :
    localIndex (p3HyperFromPotential (4*k+3) a z) f.toEmbedding ∈
      switchingAllowed (4*k+3) := by
  apply ((p3HyperFromPotential (4*k+3) a z).
    p3SwitchingAllowed_iff_coboundary_zero k a f).mpr
  exact p3HyperFromPotential_rawCoboundary_zero (4*k+3) a z f

/-- For potential-induced structures the exceptional age
criterion is JUST the absence of homogeneous packets. -/
theorem p3HyperFromPotential_toggleAllowed_iff_nonhomogeneous
    (k a : ℕ) (z : Finset (Fin a) → ZMod 2)
    (f : Fin (4*k+4) ↪o Fin a) :
    localIndex (p3HyperFromPotential (4*k+3) a z) f.toEmbedding ∈
      toggleZero (switchingAllowed (4*k+3)) ↔
    localIndex (p3HyperFromPotential (4*k+3) a z) f.toEmbedding ≠ 0 := by
  have hpar := p3HyperFromPotential_rawCoboundary_zero (4*k+3) a z f
  rw [((p3HyperFromPotential (4*k+3) a z).
    p3ToggleAllowed_iff_coboundary_zero_and_nonhomogeneous k a f)]
  simp [hpar]

end Hypertournaments
