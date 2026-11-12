import Hypertournaments.CanonicalSignPresentation
import Hypertournaments.OddToggleP1BooleanParity
import Hypertournaments.Identification

/-!
# Canonical sign disagreement excludes identification in ordinary AP

For any two finite genuine intrinsic hypertournaments L,R on the
SAME a vertices, disagreement of their canonical n-set orientation
tables on a genuine n-element subset immediately witnesses
disagreement of their ordered tuple orientations.

The conclusion plugs directly into the already kernel-verified
ordinary one-point AP identification exclusion: if one-point
sides disagree on even one canonical sign then their two fresh
points cannot be identified in an ordinary amalgam.

This works in every arity and does not require choosing a
preferred ambient order in the hypertournament language.
-/

namespace Hypertournaments

/-- A genuine difference of canonical unordered n-set orientation
signs yields an actual ordered tuple where intrinsic orientations
differ. -/
theorem canonicalSign_disagree_implies_orientation_disagree
    {n a : ℕ}
    (L R : Hyper n (Fin a))
    (Q : Finset (Fin a)) (hQ : Q.card = n)
    (hDifferent : L.canonicalSignTable Q ≠ R.canonicalSignTable Q) :
    ∃ t : Fin n ↪ Fin a, L.orient t ≠ R.orient t := by
  refine ⟨(Q.orderEmbOfFin hQ).toEmbedding, ?_⟩
  have h := hDifferent
  rw [Hyper.canonicalSignTable_at L Q hQ,
      Hyper.canonicalSignTable_at R Q hQ] at h
  exact h

/-- A disagreement already visible after embedding Boolean signs
into the two-element field gives the same actual intrinsic
orientation witness. -/
theorem canonicalF2_disagree_implies_orientation_disagree
    {n a : ℕ}
    (L R : Hyper n (Fin a))
    (Q : Finset (Fin a)) (hQ : Q.card = n)
    (hDifferent :
      p1BitToZMod (L.canonicalSignTable Q) ≠
      p1BitToZMod (R.canonicalSignTable Q)) :
    ∃ t : Fin n ↪ Fin a, L.orient t ≠ R.orient t := by
  apply canonicalSign_disagree_implies_orientation_disagree
    L R Q hQ
  intro h
  exact hDifferent (congrArg p1BitToZMod h)

/-- If actual one-point sides disagree on one canonical n-set,
their new vertices must remain distinct in EVERY ordinary
amalgam preserving their entire intrinsic orientations. -/
theorem onePoint_fresh_distinct_of_canonicalF2_disagree
    {n a d : ℕ}
    (L R : Hyper n (Fin (a+1)))
    (D : Hyper n (Fin d))
    (i j : Fin (a+1) ↪ Fin d)
    (hbase : ∀ x : Fin a, i x.castSucc = j x.castSucc)
    (hL : Preserves L D i) (hR : Preserves R D j)
    (Q : Finset (Fin (a+1))) (hQ : Q.card = n)
    (hDifferent :
      p1BitToZMod (L.canonicalSignTable Q) ≠
      p1BitToZMod (R.canonicalSignTable Q)) :
    i (Fin.last a) ≠ j (Fin.last a) := by
  exact onePoint_points_distinct_of_orient_disagree
    L R D i j hbase hL hR
    (canonicalF2_disagree_implies_orientation_disagree
      L R Q hQ hDifferent)

end Hypertournaments
