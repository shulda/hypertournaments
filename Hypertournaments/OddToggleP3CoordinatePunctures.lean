import Hypertournaments.OddToggleP3CoordinateTransversalFacts
import Hypertournaments.OddToggleP3BasePreservation

/-!
# Actual punctures of the cyclic-coordinate p3 transversals

Every cyclic-coordinate tuple gives a genuine old full transversal.
Deleting the selected vertex in block i gives *exactly* the finite
old subset obtained by deleting coordinate i from its index set,
and this punctured actual subset satisfies the same
p3IsEligibleMissingTransversal predicate used by the true
one-point side potential whenever i is eligible.

The statement is independent of zero-sum and of probabilities.
It provides the geometric bridge required to interpret abstract
punctured random source bits as genuine L/R potential coefficients.
-/

namespace Hypertournaments

/-- Erasing one genuine old vertex commutes with erasing its
coordinate from the full block index set. -/
theorem p3CoordinateTransversal_erase_vertex
    (m t : ℕ) (ht : 0 < t)
    (q : Fin m → ZMod t) (i : Fin m) :
    (p3CoordinateTransversal m t ht q).erase
      (p3BlockCoordinateVertex m t ht i (q i)) =
    ((Finset.univ : Finset (Fin m)).erase i).image
      (fun j => p3BlockCoordinateVertex m t ht j (q j)) := by
  classical
  let e : Fin m ↪ Fin (m*t) :=
    ⟨(fun j => p3BlockCoordinateVertex m t ht j (q j)),
      p3CoordinateTransversal_vertex_injective m t ht q⟩
  change ((Finset.univ : Finset (Fin m)).image e).erase (e i) =
    ((Finset.univ : Finset (Fin m)).erase i).image e
  exact (p3Finset_image_erase e (Finset.univ : Finset (Fin m)) i).symm

/-- Every actual puncture of a full block-coordinate transversal
is an eligible one-block-missing transversal when its deleted
block belongs to the prescribed eligible half. -/
theorem p3CoordinatePuncture_isEligibleMissing
    (m t : ℕ) (ht : 0 < t)
    (eligible : Finset (Fin m))
    (q : Fin m → ZMod t) (i : Fin m)
    (hi : i ∈ eligible) :
    p3IsEligibleMissingTransversal m t eligible
      ((p3CoordinateTransversal m t ht q).erase
        (p3BlockCoordinateVertex m t ht i (q i))) := by
  classical
  let Q : Finset (Fin (m*t)) := p3CoordinateTransversal m t ht q
  let u : Fin (m*t) := p3BlockCoordinateVertex m t ht i (q i)
  have hu : u ∈ Q := by
    change p3BlockCoordinateVertex m t ht i (q i) ∈
      (Finset.univ : Finset (Fin m)).image
        (fun j => p3BlockCoordinateVertex m t ht j (q j))
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hQ : Q.card = m :=
    p3CoordinateTransversal_card m t ht q
  have hcard : (Q.erase u).card = m-1 := by
    have hh := Finset.card_erase_add_one hu
    omega
  have hfilter (j : Fin m) :
      (Q.erase u).filter (fun v => p3BlockNumber t v = j.val) =
      (Q.filter (fun v => p3BlockNumber t v = j.val)).erase u := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_erase]
    tauto
  refine ⟨hcard, i, hi, ?_, ?_⟩
  · change ((Q.erase u).filter
        (fun v => p3BlockNumber t v = i.val)).card = 0
    rw [hfilter i]
    have hf : Q.filter
        (fun v => p3BlockNumber t v = i.val) = {u} :=
      p3CoordinateTransversal_block_fiber m t ht q i
    rw [hf]
    simp
  · intro j hji
    change ((Q.erase u).filter
        (fun v => p3BlockNumber t v = j.val)).card = 1
    rw [hfilter j]
    have hf : Q.filter
        (fun v => p3BlockNumber t v = j.val) =
        {p3BlockCoordinateVertex m t ht j (q j)} :=
      p3CoordinateTransversal_block_fiber m t ht q j
    rw [hf]
    have hju : p3BlockCoordinateVertex m t ht j (q j) ≠ u := by
      intro heq
      exact hji (p3CoordinateTransversal_vertex_injective m t ht q heq)
    have huj : u ≠ p3BlockCoordinateVertex m t ht j (q j) :=
      Ne.symm hju
    simp [hju, huj]

end Hypertournaments
