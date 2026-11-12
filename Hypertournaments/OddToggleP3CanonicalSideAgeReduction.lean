import Hypertournaments.OnePointAgeByNewPackets
import Hypertournaments.OddToggleP3CanonicalSides
import Hypertournaments.OddToggleP3BaseAdmissible

/-!
# Canonical p3 side age reduces to only fresh-containing packets

We have proved the common old base of the random p3 diagram
unconditionally belongs to the exceptional homogeneous-free
switching class for EVERY assignment of W. Both canonical p3
one-point sides truly preserve this old base, independently of
their eligible missing-half sets and L/R potential coefficients.

Therefore it suffices to verify just the (n+1)-packets CONTAINING
the sole new point of each side. No all-old case remains in the
actual side-age verification. This is a structural simplification
of the final p3 random-side proof, not the final side admissibility
theorem itself.

All arities n=4k+3 with k≥1 and all positive block sizes t
are treated uniformly.
-/

namespace Hypertournaments

/-- For any canonical p3 one-point side, its full exceptional
age membership follows from checking only new-point packets.
The common old base is already unconditionally admissible. -/
theorem p3CanonicalSide_admissible_of_fresh_packets
    (k t : ℕ) (hk : 1 ≤ k) (ht : 0 < t)
    (eligible : Finset (Fin (4*k+2)))
    (W L : Finset (Fin ((4*k+2)*t)) → ZMod 2)
    (hnew : ∀ f : Fin (((4*k+2)+1)+1) ↪ Fin ((4*k+2)*t+1),
      Fin.last ((4*k+2)*t) ∈ tupleVertices f →
      localIndex (p3CanonicalSide (4*k+2) t eligible W L) f ∈
        toggleZero (switchingAllowed (4*k+3))) :
    Admissible (toggleZero (switchingAllowed (4*k+3)))
      (p3CanonicalSide (4*k+2) t eligible W L) := by
  have hA : Admissible (toggleZero (switchingAllowed (4*k+3)))
      (p3HyperFromPotential ((4*k+2)+1) ((4*k+2)*t)
        (p3BasePotential (4*k+2) t W)) := by
    simpa only [show (4*k+2)+1=4*k+3 by omega] using
      (p3BaseHyper_admissible k t hk ht W)
  exact onePoint_admissible_of_new_packets
    (toggleZero (switchingAllowed (4*k+3)))
    (p3HyperFromPotential ((4*k+2)+1) ((4*k+2)*t)
      (p3BasePotential (4*k+2) t W))
    (p3CanonicalSide (4*k+2) t eligible W L)
    hA (p3CanonicalSide_preserves_base (4*k+2) t eligible W L)
    hnew

/-- Both sides of the true canonical p3 one-point diagram are
admissible once their fresh-containing packets have been certified.
Their arbitrary new-link potential families may differ. -/
theorem p3CanonicalSpan_admissible_of_fresh_packets
    (k t : ℕ) (hk : 1 ≤ k) (ht : 0 < t)
    (eligibleL eligibleR : Finset (Fin (4*k+2)))
    (W L R : Finset (Fin ((4*k+2)*t)) → ZMod 2)
    (hnewL : ∀ f : Fin (((4*k+2)+1)+1) ↪ Fin ((4*k+2)*t+1),
      Fin.last ((4*k+2)*t) ∈ tupleVertices f →
      localIndex (p3CanonicalSide (4*k+2) t eligibleL W L) f ∈
        toggleZero (switchingAllowed (4*k+3)))
    (hnewR : ∀ f : Fin (((4*k+2)+1)+1) ↪ Fin ((4*k+2)*t+1),
      Fin.last ((4*k+2)*t) ∈ tupleVertices f →
      localIndex (p3CanonicalSide (4*k+2) t eligibleR W R) f ∈
        toggleZero (switchingAllowed (4*k+3))) :
    Admissible (toggleZero (switchingAllowed (4*k+3)))
      (p3CanonicalSide (4*k+2) t eligibleL W L) ∧
    Admissible (toggleZero (switchingAllowed (4*k+3)))
      (p3CanonicalSide (4*k+2) t eligibleR W R) := by
  exact ⟨p3CanonicalSide_admissible_of_fresh_packets
      k t hk ht eligibleL W L hnewL,
    p3CanonicalSide_admissible_of_fresh_packets
      k t hk ht eligibleR W R hnewR⟩

end Hypertournaments
