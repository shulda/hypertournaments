import Hypertournaments.OddToggleP3HalfEventAndGauges
import Hypertournaments.OddToggleP3SelectedLinkSumHalf
import Hypertournaments.OddToggleP3GlobalAllTrialsExact
import Hypertournaments.OddToggleP3FullSourceWitnessHalf
import Hypertournaments.OddToggleP3GaugeChoices

/-!
# A single full-source assignment excludes EVERY finite p3 gauge and identification

The exact source-space combinatorics is already kernel-certified:
each zero-sum transversal has s+1 independent link bits and one
base W bit; for any fixed phase-dependent forbidden W choices,
the number of assignments avoiding all forbidden trial words
is an exact product. The chosen witness block size makes the
union over all degree-(m-2) gauges strictly smaller than half.

Another independent result shows that one fixed selected
zero-sum transversal has odd link-source sum in exactly half of
the full global assignments. The denominator-free finite
half-event union lemma now yields ONE global assignment with:
  (1) odd link sum on the fixed trial, excluding identification;
  (2) for EVERY supported gauge, a selected trial with one of the
      two prescribed forbidden source patterns.

The choice of the two forbidden patterns may be any function of
the supported gauge and selected trial. The remaining separate
proof obligation is to identify actual alternating mixed packets
with these abstract patterns for the canonical one-point diagram.
-/

namespace Hypertournaments

open scoped Classical

/-- Exact global source witness: for any family of phase-dependent
forbidden trial patterns indexed by ALL supported gauges, there is
one Boolean W/link assignment causing both an odd-link event on
a fixed selected zero-sum trial and at least one bad pattern for
every supported gauge. No probabilities, asymptotics or infinite
choice principles are involved. -/
theorem p3FullSource_exists_oddLink_and_badTrial_for_all_gauges
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (m : ℕ) (hm : 2 ≤ m)
    (hCard : Fintype.card G = p3WitnessBlockSize m)
    (q0 : p3SelectedTrials G (m-1))
    (chosen : Fin ((m-1)+1))
    (choice :
      (p3GaugeDomain (m*p3WitnessBlockSize m) (m-2) → Bool) →
      p3SelectedTrials G (m-1) → Bool → Bool) :
    ∃ bits : p3FullSourceSpace G (m-1) → Bool,
      (∑ i : Fin ((m-1)+1),
        p1BitToZMod
          (bits (p3FullTrialSourceIndex (m-1) (q0,Sum.inl i)))) = 1 ∧
      ∀ v : p3GaugeDomain (m*p3WitnessBlockSize m) (m-2) → Bool,
        (fun qi : p3FullSelectedSpace G (m-1) =>
          bits (p3FullTrialSourceIndex (m-1) qi)) ∉
          p3GoodSelectedTrialSet (m-1) (choice v) := by
  classical
  let s : ℕ := m-1
  let t : ℕ := p3WitnessBlockSize m
  let a : ℕ := m*t
  let Source := p3FullSourceSpace G s
  let Ω := Source → Bool
  let Gauges := p3GaugeDomain a (m-2) → Bool
  let sample : Finset Ω := Finset.univ
  let ident : Finset Ω := Finset.univ.filter
    (fun bits =>
      (∑ i : Fin (s+1),
        p1BitToZMod
          (bits (p3FullTrialSourceIndex s (q0,Sum.inl i)))) = 1)
  let gauges : Finset Gauges := Finset.univ
  let bad : Gauges → Finset Ω :=
    fun v => Finset.univ.filter
      (fun bits =>
        (fun qi : p3FullSelectedSpace G s =>
          bits (p3FullTrialSourceIndex s qi)) ∈
        p3GoodSelectedTrialSet s (choice v))
  let P : ℕ := 2^((m+1)*(t^s))
  let Q : ℕ := (2^(m+1)-2)^(t^s)
  have hs : s+2 = m+1 := by dsimp [s]; omega
  have hSampleCard : sample.card = 2^(Fintype.card Source) := by
    dsimp [sample, Ω]
    simp
  have hIdentCard :
      ident.card =
        Nat.card {bits : Ω //
          (∑ i : Fin (s+1),
            p1BitToZMod
              (bits (p3FullTrialSourceIndex s (q0,Sum.inl i)))) = 1} := by
    change
      (Finset.univ.filter
        (fun bits : Ω =>
          (∑ i : Fin (s+1),
            p1BitToZMod
              (bits (p3FullTrialSourceIndex s (q0,Sum.inl i)))) = 1)).card =
      Nat.card {bits : Ω //
        (∑ i : Fin (s+1),
          p1BitToZMod
            (bits (p3FullTrialSourceIndex s (q0,Sum.inl i)))) = 1}
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hHalf :
      2 * ident.card = sample.card := by
    have hh := p3ZeroSumFullSource_fixedTrial_linkSum_half s q0 chosen
    change
      2 * Nat.card {bits : Ω //
        (∑ i : Fin (s+1),
          p1BitToZMod
            (bits (p3FullTrialSourceIndex s (q0,Sum.inl i)))) = 1} =
      2^(Fintype.card Source) at hh
    rw [← hIdentCard, ← hSampleCard] at hh
    exact hh
  have hSamplePositive : 0 < sample.card := by
    apply Finset.card_pos.mpr
    refine ⟨(fun _ : Source => false), ?_⟩
    simp [sample]
  have hIdentPositive : 0 < ident.card := by omega
  have hBadCard (v : Gauges) :
      (bad v).card =
        Nat.card {values : Ω //
          (fun qi : p3FullSelectedSpace G s =>
            values (p3FullTrialSourceIndex s qi)) ∈
          p3GoodSelectedTrialSet s (choice v)} := by
    change
      (Finset.univ.filter
        (fun values : Ω =>
          (fun qi : p3FullSelectedSpace G s =>
            values (p3FullTrialSourceIndex s qi)) ∈
          p3GoodSelectedTrialSet s (choice v))).card =
      Nat.card {values : Ω //
        (fun qi : p3FullSelectedSpace G s =>
          values (p3FullTrialSourceIndex s qi)) ∈
        p3GoodSelectedTrialSet s (choice v)}
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hRatio : ∀ v ∈ gauges,
      P * (bad v).card ≤ Q * sample.card := by
    intro v _
    have hh := p3AllGlobalGoodTrialAssignments_exact_ratio
      (G:=G) s (choice v)
    rw [hCard, hs] at hh
    change
      P * Nat.card {values : Ω //
        (fun qi : p3FullSelectedSpace G s =>
          values (p3FullTrialSourceIndex s qi)) ∈
          p3GoodSelectedTrialSet s (choice v)} =
      Q * 2^(Fintype.card Source) at hh
    rw [← hBadCard v, ← hSampleCard] at hh
    exact le_of_eq hh
  have hGaugeCard :
      gauges.card = 2^(a.choose (m-2)) := by
    simpa only [gauges, Finset.card_univ] using
      (p3BoolGaugeChoices_card a (m-2))
  have hNumeric : 2^(a.choose (m-2)+1) * Q < P := by
    change
      2 ^ (((m*p3WitnessBlockSize m).choose (m-2)) + 1) *
        (2^(m+1)-2)^((p3WitnessBlockSize m)^(m-1)) <
      2^((m+1)*((p3WitnessBlockSize m)^(m-1)))
    exact p3Witness_fullSourceGauge_strict_half m hm
  have hSmall : 2 * gauges.card * Q < P := by
    rw [hGaugeCard]
    calc
      2 * 2^(a.choose (m-2)) * Q =
        2^(a.choose (m-2)+1) * Q := by
          rw [pow_succ]
          ring
      _ < P := hNumeric
  obtain ⟨bits, hIdentMem, hAvoid⟩ :=
    p3FiniteHalfSample_avoids_all_gauges
      sample ident gauges bad P Q
      hHalf hIdentPositive hRatio hSmall
  refine ⟨bits, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hIdentMem).2
  · intro v hGood
    exact (hAvoid v (Finset.mem_univ v))
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hGood⟩)

end Hypertournaments
