import Hypertournaments.RootedOddSuspensionSigns
import Hypertournaments.EvenSuspensionTwoThreeFacets

/-!
# Exact three-pad geometry and rooted potential erasure laws

For a local packet with exactly three padding vertices, erasing a
present pad leaves two pads and reads the old source canonical sign.
Erasing a nonpad leaves three pads and reads the root potential of
the old projection with that old vertex erased.

The root potential has three useful exact cases:
* erasing a present root reads the old source sign on the full set;
* erasing a different vertex while the root remains gives true;
* if the root is absent, erasing a vertex reads the source sign on
  the set augmented by the root.

These are the precise finite-set identities required for the
two three-pad local-type subcases of the odd suspension.
-/

namespace Hypertournaments

/-- Erasing one of the three pads reads the source n-sign on the
unchanged old projection. -/
theorem rootedOddSignTable_erase_pad_three
    {n : ℕ} (m a : ℕ) (A : Hyper n (Fin a)) (root : Fin a)
    (Q : Finset (Fin (m+a)))
    (hthree : (evenPadProjection m a Q).card = 3)
    (p : Fin m) (hp : p ∈ evenPadProjection m a Q) :
    rootedOddSuspensionSignTable m a A root
        (Q.erase (evenPadShift m a p)) =
      A.canonicalSignTable (evenOldProjection m a Q) := by
  have htwo :
      (evenPadProjection m a
        (Q.erase (evenPadShift m a p))).card = 2 := by
    rw [evenPadProjection_erase_pad]
    have h := Finset.card_erase_add_one hp
    omega
  unfold rootedOddSuspensionSignTable
  simp [htwo, evenOldProjection_erase_pad]

/-- Erasing a nonpad from a three-pad packet reads the root potential
after deleting the corresponding old vertex. -/
theorem rootedOddSignTable_erase_old_three
    {n : ℕ} (m a : ℕ) (A : Hyper n (Fin a)) (root : Fin a)
    (Q : Finset (Fin (m+a)))
    (hthree : (evenPadProjection m a Q).card = 3)
    (u : Fin a) :
    rootedOddSuspensionSignTable m a A root
      (Q.erase (evenOldShift m a u)) =
      rootedOddPotentialSignTable A root
        ((evenOldProjection m a Q).erase u) := by
  have hcard :
      (evenPadProjection m a
        (Q.erase (evenOldShift m a u))).card = 3 := by
    rw [evenPadProjection_erase_nonpad m a Q
      (evenOldShift m a u) (evenOldShift_not_mem_pad m a u)]
    exact hthree
  rw [rootedOddSuspensionSignTable_threePads m a A root _ hcard]
  rw [evenOldProjection_erase_old]

/-- When the root belongs to a finite old set, erasing it makes the
potential read exactly the source sign of that full old set. -/
theorem rootedOddPotential_erase_root
    {n a : ℕ} (A : Hyper n (Fin a)) (root : Fin a)
    (F : Finset (Fin a)) (hroot : root ∈ F) :
    rootedOddPotentialSignTable A root (F.erase root) =
      A.canonicalSignTable F := by
  have hnot : root ∉ F.erase root := by simp
  have hreconstruct : insert root (F.erase root) = F :=
    Finset.insert_erase hroot
  unfold rootedOddPotentialSignTable
  simp [hnot, hreconstruct]

/-- Erasing any other vertex of an old set still containing the root
makes the root potential positive. -/
theorem rootedOddPotential_erase_nonroot
    {n a : ℕ} (A : Hyper n (Fin a)) (root : Fin a)
    (F : Finset (Fin a))
    (hroot : root ∈ F) (u : Fin a) (hru : root ≠ u) :
    rootedOddPotentialSignTable A root (F.erase u) = true := by
  have hin : root ∈ F.erase u :=
    Finset.mem_erase.mpr ⟨hru, hroot⟩
  simp [rootedOddPotentialSignTable, hin]

/-- When the root is outside the original old set, erasing a vertex
and evaluating the root potential is exactly the old sign on the
root-augmented facet. -/
theorem rootedOddPotential_erase_of_root_absent
    {n a : ℕ} (A : Hyper n (Fin a)) (root : Fin a)
    (F : Finset (Fin a))
    (hroot : root ∉ F) (u : Fin a) :
    rootedOddPotentialSignTable A root (F.erase u) =
      A.canonicalSignTable (insert root (F.erase u)) := by
  have hnot : root ∉ F.erase u := by
    intro h
    exact hroot (Finset.mem_of_mem_erase h)
  simp [rootedOddPotentialSignTable, hnot]

end Hypertournaments
