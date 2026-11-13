import Hypertournaments.OddToggleP3TrialPolarityCount

/-!
# Fixed forbidden W endpoint choice despite random p3 link bits

In the actual canonical joint, old < left < right, the forbidden
right-side endpoint has value beta = alternating interior phase.

Fix a gauge shift and any deterministic right-endpoint functional.
Once the mixed interior is alternating with phase b, the random
link bits are forced to equal alternating(b) XOR shift.
Consequently the forbidden W choice equals
  b XOR rightSum(alternating(b) XOR shift).
This fixed choice depends on the gauge and phase, not on
unconditioned link bits, even though the endpoint itself reads
those random bits.

This is abstract Boolean algebra; the actual joint/side-potential
facet identification is still a separate proof obligation.
-/

namespace Hypertournaments

def p3FixedBadWChoice
    (m : ℕ) (shift : Fin m → Bool)
    (rightSum : (Fin m → Bool) → Bool) (phase : Bool) : Bool :=
  phase ^^ rightSum
    (p3BoolTranslate shift (p3AlternatingWord m phase))

/-- Alternating interior uniquely determines its link-source word. -/
theorem p3Links_forced_by_alternating_interior
    (m : ℕ) (shift link : Fin m → Bool) (phase : Bool)
    (hphase : p3BoolTranslate shift link =
      p3AlternatingWord m phase) :
    link = p3BoolTranslate shift (p3AlternatingWord m phase) := by
  calc
    link = p3BoolTranslate shift (p3BoolTranslate shift link) :=
      (p3BoolTranslate_involutive shift link).symm
    _ = p3BoolTranslate shift (p3AlternatingWord m phase) :=
      congrArg (p3BoolTranslate shift) hphase

/-- For a fixed alternating interior, the forbidden W endpoint
condition has no remaining dependence on the random link word. -/
theorem p3RightEndpoint_badW_iff
    (m : ℕ) (shift link : Fin m → Bool)
    (rightSum : (Fin m → Bool) → Bool) (phase base : Bool)
    (hphase : p3BoolTranslate shift link =
      p3AlternatingWord m phase) :
    ((base ^^ rightSum link) = phase) ↔
      base = p3FixedBadWChoice m shift rightSum phase := by
  rw [p3Links_forced_by_alternating_interior
    m shift link phase hphase]
  unfold p3FixedBadWChoice
  have hx (a b c : Bool) : ((a ^^ b) = c) ↔ (a = (c ^^ b)) := by
    cases a <;> cases b <;> cases c <;> decide
  exact hx base
    (rightSum (p3BoolTranslate shift (p3AlternatingWord m phase)))
    phase

/-- Two forbidden trial words are exactly the alternating
interior and their phase-dependent W-bit prescriptions. -/
theorem p3TrialPacketBits_mem_badPattern_iff
    (m : ℕ) (choice : Bool → Bool)
    (interior : Fin m → Bool) (base : Bool) :
    p3TrialPacketBits m interior base ∈
      ((Finset.univ : Finset Bool).image
        (p3BadPattern m choice)) ↔
      ∃ phase : Bool,
        interior = p3AlternatingWord m phase ∧
        base = choice phase := by
  classical
  constructor
  · intro h
    obtain ⟨phase, _, hh⟩ := Finset.mem_image.mp h
    refine ⟨phase, ?_, ?_⟩
    · funext i
      have hi := congrFun hh (Sum.inl i)
      change p3AlternatingWord m phase i = interior i at hi
      exact hi.symm
    · have hi := congrFun hh (Sum.inr ())
      change choice phase = base at hi
      exact hi.symm
  · rintro ⟨phase, hinter, hbase⟩
    apply Finset.mem_image.mpr
    refine ⟨phase, Finset.mem_univ _, ?_⟩
    funext s
    cases s with
    | inl i =>
        change p3AlternatingWord m phase i = interior i
        exact (congrFun hinter i).symm
    | inr u =>
        cases u
        change choice phase = base
        exact hbase.symm

/-- For fixed gauge and fixed endpoint functional, the actual
random trial condition is exactly membership in two FIXED
phase-dependent forbidden source-bit patterns. -/
theorem p3RightEndpoint_badEvent_iff_badPatterns
    (m : ℕ) (shift link : Fin m → Bool)
    (rightSum : (Fin m → Bool) → Bool) (base : Bool) :
    (∃ phase : Bool,
      p3BoolTranslate shift link = p3AlternatingWord m phase ∧
      ((base ^^ rightSum link) = phase)) ↔
    p3TrialPacketBits m (p3BoolTranslate shift link) base ∈
      ((Finset.univ : Finset Bool).image
        (p3BadPattern m (p3FixedBadWChoice m shift rightSum))) := by
  rw [p3TrialPacketBits_mem_badPattern_iff]
  constructor
  · rintro ⟨phase, hphase, hbeta⟩
    refine ⟨phase, hphase, ?_⟩
    exact (p3RightEndpoint_badW_iff
      m shift link rightSum phase base hphase).mp hbeta
  · rintro ⟨phase, hphase, hbase⟩
    refine ⟨phase, hphase, ?_⟩
    exact (p3RightEndpoint_badW_iff
      m shift link rightSum phase base hphase).mpr hbase

end Hypertournaments
