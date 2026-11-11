import Hypertournaments.OddToggleP3SwitchingParity
import Hypertournaments.SwitchingShift

/-!
# Precise p3 age splitting: parity plus nonhomogeneity

For n=4k+3 the homogeneous index zero belongs to the switching
family. Toggling index zero therefore forbids it and leaves the
other switching indices unchanged.

On a genuine increasing packet we may equivalently verify:
  (i) the unsigned coboundary of canonical orientations is zero;
  (ii) the packet is not homogeneous (localIndex is not zero).

The first criterion is global F₂ parity, and the second is exactly
what protected opposite-parity zero facets will enforce for each
random one-point side. This lemma isolates these independent jobs.
-/

namespace Hypertournaments

/-- Every switching family in arity 4k+3 contains the homogeneous
index zero, since its central index is even. -/
theorem p3Zero_mem_switchingAllowed (k : ℕ) :
    0 ∈ switchingAllowed (4*k+3) := by
  change 0 ≤ centralIndex (4*k+3) ∧
    0 % 2 = centralIndex (4*k+3) % 2
  unfold centralIndex
  omega

/-- A genuine p3 packet belongs to the exceptional forbidden-
homogeneous switching family iff its raw canonical coboundary
vanishes and its actual local index is nonzero. -/
theorem Hyper.p3ToggleAllowed_iff_coboundary_zero_and_nonhomogeneous
    (k a : ℕ) (A : Hyper (4*k+3) (Fin a))
    (f : Fin (4*k+4) ↪o Fin a) :
    localIndex A f.toEmbedding ∈
        toggleZero (switchingAllowed (4*k+3)) ↔
      (coboundary
        (fun Q => p1BitToZMod (A.canonicalSignTable Q))
        (tupleVertices f.toEmbedding) = 0 ∧
       localIndex A f.toEmbedding ≠ 0) := by
  have hmem := p3Zero_mem_switchingAllowed k
  change (if localIndex A f.toEmbedding = 0
      then localIndex A f.toEmbedding ∉ switchingAllowed (4*k+3)
      else localIndex A f.toEmbedding ∈ switchingAllowed (4*k+3)) ↔
    (coboundary
      (fun Q => p1BitToZMod (A.canonicalSignTable Q))
      (tupleVertices f.toEmbedding) = 0 ∧
     localIndex A f.toEmbedding ≠ 0)
  by_cases hz : localIndex A f.toEmbedding = 0
  · simp [hz, hmem]
  · simpa [hz] using
      (A.p3SwitchingAllowed_iff_coboundary_zero k a f)

end Hypertournaments
