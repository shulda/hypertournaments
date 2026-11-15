import Hypertournaments.OddToggleP3ActualJointGauge
import Hypertournaments.OddToggleP3CochainSideLinks
import Hypertournaments.OddToggleP3BasePreservation

/-!
# Every genuine p3 switching joint extending two potentials has a gauge

Let E be an arbitrary intrinsic p3 switching hypertournament joint on
Fin(a+2) and old an injective copy of the old base. Suppose on
old m-sets Q the two genuine one-new orientation links of E equal
the coboundaries of given left/right side potential tables zL,zR,
and the two potentials agree on all old m-sets. Then their combined
contracted potential h on the old base satisfies the *actual* link
identity alpha+beta=delta h, exactly as required by the existing
all-genuine-joints mixed gauge theorem.

Consequently the actual mixed cochain extracted from E is h+delta u
on every old (m-1)-set. This is not a preferred joint construction.

The link hypotheses are explicit and will be discharged by the
actual order-preserving one-point inclusions of the random sides.
This theorem alone does not establish random-side admissibility or
ordinary non-amalgamation.
-/

namespace Hypertournaments

/-- Under exact agreement with the two one-point potential side links,
every actual switching joint has the universal mixed gauge normal form. -/
theorem Hyper.p3ActualJoint_gauge_of_side_potentials
    (k a : ℕ) (root : Fin a)
    (E : Hyper (4*k+3) (Fin (a+2)))
    (hE : Admissible (switchingAllowed (4*k+3)) E)
    (old : Fin a ↪ Fin (a+2))
    (l r : Fin (a+2)) (hlr : l ≠ r)
    (hFresh : ∀ v : Fin a, old v ≠ l ∧ old v ≠ r)
    (zL zR : Finset (Fin (a+2)) → ZMod 2)
    (hLeft : ∀ Q : Finset (Fin a), Q.card = 4*k+2 →
      p1BitToZMod
        (E.canonicalSignTable (insert l (Q.image old))) =
      coboundary zL (insert l (Q.image old)))
    (hRight : ∀ Q : Finset (Fin a), Q.card = 4*k+2 →
      p1BitToZMod
        (E.canonicalSignTable (insert r (Q.image old))) =
      coboundary zR (insert r (Q.image old)))
    (hBase : ∀ Q : Finset (Fin a), Q.card = 4*k+2 →
      zL (Q.image old) = zR (Q.image old)) :
    ∃ u : Finset (Fin a) → ZMod 2,
      ∀ U : Finset (Fin a), U.card = 4*k+1 →
        contractAt r
          (contractAt l
            (fun T : Finset (Fin (a+2)) =>
              p1BitToZMod (E.canonicalSignTable T)))
          (U.image old) =
        (contractAt l zL (U.image old) +
          contractAt r zR (U.image old)) +
        coboundary u U := by
  let h : Finset (Fin a) → ZMod 2 :=
    fun U => contractAt l zL (U.image old) +
      contractAt r zR (U.image old)
  have hlink : ∀ Q : Finset (Fin a), Q.card = 4*k+2 →
      p1BitToZMod (E.canonicalSignTable (insert l (Q.image old))) +
      p1BitToZMod (E.canonicalSignTable (insert r (Q.image old))) =
      coboundary h Q := by
    intro Q hQ
    let S : Finset (Fin (a+2)) := Q.image old
    have hl : l ∉ S := by
      intro hmem
      obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hmem
      exact (hFresh v).1 hv
    have hr : r ∉ S := by
      intro hmem
      obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hmem
      exact (hFresh v).2 hv
    have hside : coboundary zL (insert l S) +
        coboundary zR (insert r S) =
      coboundary
        (fun T => contractAt l zL T + contractAt r zR T) S :=
      p3SideLink_sum_eq_coboundary
        l r zL zR S hl hr (hBase Q hQ)
    have hrestrict : coboundary
        (fun T => contractAt l zL T + contractAt r zR T) S =
      coboundary h Q := by
      apply p3Coboundary_image_injective old h
        (fun T => contractAt l zL T + contractAt r zR T)
      intro U
      rfl
    calc
      p1BitToZMod (E.canonicalSignTable (insert l (Q.image old))) +
          p1BitToZMod (E.canonicalSignTable (insert r (Q.image old))) =
        coboundary zL (insert l S) +
          coboundary zR (insert r S) := by
            rw [hLeft Q hQ, hRight Q hQ]
      _ = coboundary
          (fun T => contractAt l zL T + contractAt r zR T) S := hside
      _ = coboundary h Q := hrestrict
  obtain ⟨u, hu⟩ :=
    E.p3ActualJoint_has_mixed_gauge
      k a root hE old l r hlr hFresh h hlink
  refine ⟨u, ?_⟩
  intro U hU
  exact hu U hU

end Hypertournaments
