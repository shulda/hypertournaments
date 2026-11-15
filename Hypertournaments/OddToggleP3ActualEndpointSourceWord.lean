import Hypertournaments.OddToggleP3RealSelectedSideLinks
import Hypertournaments.OddToggleP3PotentialPresentation

/-!
# Real selected p3 endpoint Boolean sign is W XOR eligible link parity

The genuine canonical p3 one-point side orienting a selected
old full transversal Q plus its sole fresh vertex has F₂ sign
W(Q)+sum_i L_i(Q\{v_i}) over the eligible missing blocks.
The already kernel-checked real source bridge identifies every
coefficient with the corresponding selected full global source
bit. This module converts that F₂ identity to a literal Boolean
XOR of the true independent W bit and the parity functional
of the actual eligible link-source word.

The right endpoint functional is now a fixed deterministic
functional on Fin m → Bool, so the previously certified
p3FixedBadWChoice phase formula can be applied without
assumptions of independence or preferred joint orientation.
-/

namespace Hypertournaments

open scoped Classical

/-- The genuine selected globally independent Boolean link
source word indexed by the old deleted block. -/
def p3ActualSelectedLinkWord
    {G : Type*} [AddCommGroup G] (s : ℕ)
    (bits : p3FullSourceSpace G s → Bool)
    (q : p3SelectedTrials G s) : Fin (s+1) → Bool :=
  fun i => bits (p3FullTrialSourceIndex s (q,Sum.inl i))

/-- The right (or left) endpoint's deterministic eligible
link parity functional, on an arbitrary link Boolean word. -/
noncomputable def p3EligibleLinkParity
    (s : ℕ) (eligible : Finset (Fin (s+1)))
    (link : Fin (s+1) → Bool) : Bool :=
  p3ZMod2ToBool
    (∑ i : Fin (s+1),
      if i ∈ eligible then p1BitToZMod (link i) else 0)

/-- Every genuine canonical one-point p3 side endpoint on a
selected zero-sum old full transversal is exactly independent
W(q) XOR the deterministic eligible link parity of the
selected global source word. -/
theorem p3ActualSelectedCanonicalSide_endpointBool_eq_W_xor_linkParity
    (s t : ℕ) (ht : 0 < t)
    (eligible : Finset (Fin (s+1)))
    (bits : p3FullSourceSpace (ZMod t) s → Bool)
    (q : p3SelectedTrials (ZMod t) s) :
    (p3CanonicalSide (s+1) t eligible
        (p3RealWFromSources s t ht bits)
        (p3RealLinkFromSources s t ht bits)).canonicalSignTable
      (insert (Fin.last ((s+1)*t))
        ((p3CoordinateTransversal (s+1) t ht q.1).image
          (onePointBaseEmbedding ((s+1)*t)))) =
    (bits (p3FullTrialSourceIndex s (q,Sum.inr ())) ^^
      p3EligibleLinkParity s eligible
        (p3ActualSelectedLinkWord s bits q)) := by
  classical
  let raw : Bool :=
    (p3CanonicalSide (s+1) t eligible
        (p3RealWFromSources s t ht bits)
        (p3RealLinkFromSources s t ht bits)).canonicalSignTable
      (insert (Fin.last ((s+1)*t))
        ((p3CoordinateTransversal (s+1) t ht q.1).image
          (onePointBaseEmbedding ((s+1)*t))))
  let base : Bool := bits (p3FullTrialSourceIndex s (q,Sum.inr ()))
  let rest : ZMod 2 :=
    ∑ i : Fin (s+1),
      if i ∈ eligible then
        p1BitToZMod (bits (p3FullTrialSourceIndex s (q,Sum.inl i)))
      else 0
  have hEq : p1BitToZMod raw = p1BitToZMod base + rest :=
    p3RealSelectedCanonicalSide_link_eq_globalSources
      s t ht eligible bits q
  have hRound : p1BitToZMod (p3ZMod2ToBool rest) = rest :=
    p3BitToZMod_roundtrip rest
  have hXor :
      p1BitToZMod (base ^^ p3ZMod2ToBool rest) =
        p1BitToZMod base + rest := by
    rw [p1BitToZMod_xor,hRound]
  have hinj : Function.Injective p1BitToZMod := by decide
  have hBool : raw = (base ^^ p3ZMod2ToBool rest) :=
    hinj (hEq.trans hXor.symm)
  change raw = (base ^^ p3EligibleLinkParity s eligible
    (p3ActualSelectedLinkWord s bits q))
  exact hBool

end Hypertournaments
