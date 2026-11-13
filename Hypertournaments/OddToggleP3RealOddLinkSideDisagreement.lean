import Lean.Elab.Tactic.Omega
import Hypertournaments.OddToggleP3RealTwoSideLinkParity
import Hypertournaments.OddToggleP3RealEndpointMismatchHalf
import Hypertournaments.OddToggleP3CanonicalJointPacketImages

/-!
# Odd selected link source parity forces actual one-point side disagreement

For the two real p3 canonical sides supported on complementary
eligible missing-block families, the selected endpoint F₂ signs
sum to the parity of their independent selected link sources.
If the latter is 1 for one real zero-sum full transversal,
the two TRUE side canonical signs on the same old-plus-new
n-element set differ. The already certified intrinsic finite
sign-table-to-orientation lemma then gives a genuine injective
n-tuple witnessing side disagreement.

This explicitly excludes identifying the two new vertices
in any ordinary amalgam; no preferred joint, no probability,
and no hidden ordering in the hypertournament language.
-/

namespace Hypertournaments

open scoped Classical

/-- Odd parity of the actual selected link-source word on
one zero-sum transversal produces an actual n-tuple on which
the two canonical one-point sides have different orientations. -/
theorem p3RealOddLink_forces_side_tuple_disagreement
    (k t : ℕ) (ht : 0 < t)
    (eligible : Finset (Fin (4*k+2)))
    (bits : p3FullSourceSpace (ZMod t) (4*k+1) → Bool)
    (q : p3SelectedTrials (ZMod t) (4*k+1))
    (hOdd :
      (∑ i : Fin (4*k+2),
        p1BitToZMod (bits
          (p3FullTrialSourceIndex (4*k+1) (q,Sum.inl i)))) =
      (1 : ZMod 2)) :
    ∃ z : Fin (4*k+3) ↪ Fin ((4*k+2)*t+1),
      (p3CanonicalSide (4*k+2) t eligible
        (p3RealWFromSources (4*k+1) t ht bits)
        (p3RealLinkFromSources (4*k+1) t ht bits)).orient z ≠
      (p3CanonicalSide (4*k+2) t (Finset.univ \ eligible)
        (p3RealWFromSources (4*k+1) t ht bits)
        (p3RealLinkFromSources (4*k+1) t ht bits)).orient z := by
  classical
  let m : ℕ := 4*k+2
  let s : ℕ := 4*k+1
  let a : ℕ := m*t
  let Q : Finset (Fin a) :=
    p3CoordinateTransversal m t ht q.1
  let S : Finset (Fin (a+1)) :=
    insert (Fin.last a) (Q.image (onePointBaseEmbedding a))
  let W : Finset (Fin a) → ZMod 2 :=
    p3RealWFromSources s t ht bits
  let Link : Finset (Fin a) → ZMod 2 :=
    p3RealLinkFromSources s t ht bits
  let L := p3CanonicalSide m t eligible W Link
  let R := p3CanonicalSide m t (Finset.univ \ eligible) W Link
  have hQ : Q.card = m := p3CoordinateTransversal_card m t ht q.1
  have hS : S.card = 4*k+3 := by
    have h := p3CanonicalSide_oldPlusNew_card a m Q hQ
    change S.card = m+1 at h
    dsimp only [m] at h
    omega
  have hPairSum :=
    p3RealSelectedCanonicalLinks_sum_eq_allLinkSources
      s t ht eligible bits q
  have hSumOne :
      p3RealSelectedCanonicalLink s t ht eligible bits q +
        p3RealSelectedCanonicalLink s t ht
          (Finset.univ \ eligible) bits q = 1 :=
    hPairSum.trans hOdd
  have hNe : L.canonicalSignTable S ≠ R.canonicalSignTable S := by
    intro hEq
    have hEqF := congrArg p1BitToZMod hEq
    change
      p3RealSelectedCanonicalLink s t ht eligible bits q =
      p3RealSelectedCanonicalLink s t ht
        (Finset.univ \ eligible) bits q at hEqF
    rw [hEqF] at hSumOne
    have hDouble : ∀ x : ZMod 2, x+x=0 := by decide
    rw [hDouble] at hSumOne
    exact (by decide : (0 : ZMod 2) ≠ 1) hSumOne
  exact Hyper.orient_disagree_of_canonicalSignTable_disagree
    L R S hS hNe

end Hypertournaments
