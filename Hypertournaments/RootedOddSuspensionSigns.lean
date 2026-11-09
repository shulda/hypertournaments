import Hypertournaments.EvenSuspensionRecovery

/-!
# Concrete rooted two-coordinate suspension for odd arities

For a distinguished old root r, define the root potential on old
subsets F by the constant positive sign if r∈F, and by the canonical
source sign of {r}∪F otherwise. On high (n+2)-sets, two pad vertices
read the original n-orientation; three pads read this potential;
all other high subsets get positive sign.

This is a total ordered sign table used to construct an intrinsically
alternating (n+2)-hypertournament. It records no auxiliary linear
order in the mathematical language.

The construction can be used for all n, but its local-type-control
theorem will require odd n and a compatible root in the common base.
This file proves only the literal two- and three-pad table identities.
-/

namespace Hypertournaments

/-- The root potential of an intrinsic old hypertournament.
The value on wrong-sized sets is irrelevant to local orientation. -/
def rootedOddPotentialSignTable
    {n k : ℕ} (A : Hyper n (Fin k)) (root : Fin k)
    (Q : Finset (Fin k)) : Bool :=
  if root ∈ Q then true
  else A.canonicalSignTable (insert root Q)

/-- Literal high ordered sign table for rooted odd-arity suspension. -/
def rootedOddSuspensionSignTable
    {n : ℕ} (m k : ℕ) (A : Hyper n (Fin k))
    (root : Fin k) (Q : Finset (Fin (m + k))) : Bool :=
  if (evenPadProjection m k Q).card = 2 then
    A.canonicalSignTable (evenOldProjection m k Q)
  else if (evenPadProjection m k Q).card = 3 then
    rootedOddPotentialSignTable A root (evenOldProjection m k Q)
  else true

/-- Every two-pad old-subset packet reads exactly the source
canonical orientation, independently of the chosen root. -/
theorem rootedOddSuspensionSignTable_twoPads
    {n : ℕ} (m k : ℕ) (A : Hyper n (Fin k))
    (root : Fin k)
    (x y : Fin m) (Q : Finset (Fin k)) (hxy : x ≠ y) :
    rootedOddSuspensionSignTable m k A root
        (evenPaddedPacket m k x y Q) =
      A.canonicalSignTable Q := by
  unfold rootedOddSuspensionSignTable
  rw [evenPadProjection_paddedPacket_card m k x y Q hxy]
  simp only [if_pos rfl, evenOldProjection_paddedPacket]

/-- A three-pad packet reads the actual root-potential sign. -/
theorem rootedOddSuspensionSignTable_threePads
    {n : ℕ} (m k : ℕ) (A : Hyper n (Fin k))
    (root : Fin k)
    (Q : Finset (Fin (m + k)))
    (hthree : (evenPadProjection m k Q).card = 3) :
    rootedOddSuspensionSignTable m k A root Q =
      rootedOddPotentialSignTable A root (evenOldProjection m k Q) := by
  unfold rootedOddSuspensionSignTable
  simp [hthree]

/-- Actual intrinsic higher-arity hypertournament obtained from the
rooted odd suspension sign table. -/
def Hyper.rootedOddSuspension
    {n : ℕ} (m k : ℕ) (A : Hyper n (Fin k))
    (root : Fin k) : Hyper (n + 2) (Fin (m + k)) :=
  Hyper.fromOrderedSigns (rootedOddSuspensionSignTable m k A root)

end Hypertournaments
