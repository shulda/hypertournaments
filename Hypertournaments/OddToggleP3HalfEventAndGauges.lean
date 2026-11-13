import Mathlib.Tactic.Ring
import Hypertournaments.OddToggleP3FractionUnionBound

/-!
# Intersect a half-sized identification event with avoidance of all gauges

The last step of the exceptional p3 non-AP proof must choose W/L/R
bits both excluding fresh-vertex identification and preventing
every distinct-vertex joint. The identification-excluding event
has exactly half the finite sample space (proved separately).
A union bound over all gauge-compatible bad events is strictly
smaller than half.

This finite theorem combines those facts using integer
cross-multiplication only, avoiding floor/ceiling and measures:
 if 2*|ident|=|sample| and for every gauge
 P*|bad_i|<=Q*|sample|, while
 2*|gauges|*Q<P,
then ident contains an assignment avoiding all bad gauges.

The exact p3 identification event cardinality and actual packet
interpretation remain separate obligations.
-/

namespace Hypertournaments

/-- A prescribed finite half-sized event intersects the
complement of every gauge-bad event whenever the total
fractional gauge bound is strictly smaller than one half. -/
theorem p3FiniteHalfSample_avoids_all_gauges
    {Ω I : Type*} [DecidableEq Ω]
    (sample ident : Finset Ω) (gauges : Finset I)
    (bad : I → Finset Ω) (P Q : ℕ)
    (hhalf : 2 * ident.card = sample.card)
    (hident : 0 < ident.card)
    (hRatio : ∀ i ∈ gauges,
      P * (bad i).card ≤ Q * sample.card)
    (hSmall : 2 * gauges.card * Q < P) :
    ∃ x ∈ ident, ∀ i ∈ gauges, x ∉ bad i := by
  classical
  let badOnIdent : I → Finset Ω :=
    fun i => bad i ∩ ident
  have hsubset : ∀ i ∈ gauges, badOnIdent i ⊆ ident := by
    intro i _
    exact Finset.inter_subset_right
  have hRatio' : ∀ i ∈ gauges,
      P * (badOnIdent i).card ≤ (2 * Q) * ident.card := by
    intro i hi
    have hcard : (badOnIdent i).card ≤ (bad i).card :=
      Finset.card_le_card Finset.inter_subset_left
    calc
      P * (badOnIdent i).card ≤ P * (bad i).card :=
        Nat.mul_le_mul_left P hcard
      _ ≤ Q * sample.card := hRatio i hi
      _ = (2 * Q) * ident.card := by
        rw [← hhalf]
        ring
  have hSmall' : gauges.card * (2*Q) < P := by
    have hEq : gauges.card * (2*Q) =
        2*gauges.card*Q := by ring
    rwa [hEq]
  obtain ⟨x, hx, hno⟩ :=
    p3FiniteUnionBound_of_fraction_bound
      ident gauges badOnIdent P (2*Q)
      hident hsubset hRatio' hSmall'
  refine ⟨x,hx,?_⟩
  intro i hi hbad
  exact hno i hi (Finset.mem_inter.mpr ⟨hbad,hx⟩)

end Hypertournaments
