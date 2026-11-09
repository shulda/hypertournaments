import Hypertournaments.EvenSuspensionConcreteObstruction
import Hypertournaments.OnePointJoint

/-!
# Transfer from an ordinary lower one-point nonamalgamation witness

A lower canonical one-point span with no ordinary amalgam has genuine
orientation disagreement; otherwise its two sides can be identified.
It also cannot have a distinct-vertex amalgam on the canonical joint.
These are the two assumptions of the concrete even suspension
obstruction theorem. Consequently the actual even suspension excludes
ordinary AP for both the exactly shifted family and the family with
the homogeneous local type 0 added.

This lemma does not assert that every AP failure has a one-point
witness; that normalization remains separate.
-/

namespace Hypertournaments

/-- Shifting all allowed indices up by one, then down by one,
recovers precisely the original set. -/
theorem shiftedAllowed_evenRaisedTypes (S : Set ℕ) :
    shiftedAllowed (evenRaisedTypes S) = S := by
  ext d
  constructor
  · intro hd
    change d + 1 ∈ evenRaisedTypes S at hd
    obtain ⟨e, he, hde⟩ := hd
    have heq : d = e := by omega
    simpa [heq] using he
  · intro hd
    change d + 1 ∈ evenRaisedTypes S
    exact ⟨d, hd, rfl⟩

/-- Adding the zero type does not change the shifted family,
since no successor equals zero. -/
theorem shiftedAllowed_evenRaisedTypes_insert_zero (S : Set ℕ) :
    shiftedAllowed (Set.insert 0 (evenRaisedTypes S)) = S := by
  ext d
  constructor
  · intro hd
    change d + 1 ∈ Set.insert 0 (evenRaisedTypes S) at hd
    rcases (Set.mem_insert_iff).mp hd with hz | hrest
    · omega
    · obtain ⟨e, he, hde⟩ := hrest
      have heq : d = e := by omega
      simpa [heq] using he
  · intro hd
    change d + 1 ∈ Set.insert 0 (evenRaisedTypes S)
    exact (Set.mem_insert_iff).2 (Or.inr ⟨d, hd, rfl⟩)

/-- A canonical one-point span with no ordinary amalgam
must have different orientations on the two one-point sides,
because identical sides would give an amalgam by identification. -/
theorem onePointNoAmalgam_has_disagreement
    {n a : ℕ} (S : Set ℕ)
    (A : Hyper n (Fin a))
    (L R : Hyper n (Fin (a + 1)))
    (hL : Admissible S L)
    (hno : ¬ OnePointHasAmalgam S A L R) :
    ∃ t : Fin n ↪ Fin (a + 1),
      L.orient t ≠ R.orient t := by
  classical
  by_contra hdiff
  have heq : ∀ t : Fin n ↪ Fin (a + 1),
      L.orient t = R.orient t := by
    intro t
    by_contra ht
    exact hdiff ⟨t, ht⟩
  let idEmb : Fin (a + 1) ↪ Fin (a + 1) :=
    ⟨id, by intro x y h; exact h⟩
  have hLL : Preserves L L idEmb := by
    intro t
    rfl
  have hRL : Preserves R L idEmb := by
    intro t
    change L.orient t = R.orient t
    exact heq t
  apply hno
  exact ⟨a + 1, L, idEmb, idEmb, hL, hLL, hRL,
    by intro x; rfl⟩

/-- A canonical distinct joint would itself be an ordinary amalgam
of the same lower one-point span. -/
theorem onePointNoAmalgam_no_canonical_joint
    {n a : ℕ} (S : Set ℕ)
    (A : Hyper n (Fin a))
    (L R : Hyper n (Fin (a + 1)))
    (hno : ¬ OnePointHasAmalgam S A L R) :
    ∀ E : Hyper n (Fin (a + 2)),
      Admissible S E →
      Preserves L E (leftJointInclusion a) →
      Preserves R E (rightJointInclusion a) → False := by
  intro E hE hEL hER
  apply hno
  refine ⟨a + 2, E, leftJointInclusion a, rightJointInclusion a,
    hE, hEL, hER, ?_⟩
  intro x
  change x.castSucc.castSucc = rightJointInclusion a x.castSucc
  exact (rightJointInclusion_old a x).symm

/-- Both standard high type choices lack ordinary AP whenever
the low even-arity class has a bad canonical one-point span. -/
theorem not_hasAP_evenSuspension_of_bad_onePoint
    (k a m : ℕ) (S : Set ℕ)
    (A : Hyper (2 * k) (Fin a))
    (L R : Hyper (2 * k) (Fin (a + 1)))
    (hA : Admissible S A)
    (hL : Admissible S L)
    (hR : Admissible S R)
    (hAL : Preserves A L (onePointBaseEmbedding a))
    (hAR : Preserves A R (onePointBaseEmbedding a))
    (hcentral : k ∈ S)
    (hm : 2 ^ Fintype.card (Fin (2 * k + 1) ↪ Fin (a + 2)) < m)
    (hno : ¬ OnePointHasAmalgam S A L R) :
    (¬ HasAP (2 * k + 2) (evenRaisedTypes S)) ∧
    (¬ HasAP (2 * k + 2) (Set.insert 0 (evenRaisedTypes S))) := by
  have hlow := onePointNoAmalgam_has_disagreement S A L R hL hno
  have hNoLow := onePointNoAmalgam_no_canonical_joint S A L R hno
  have hraise : ∀ d : ℕ, d ∈ S → d + 1 ∈ evenRaisedTypes S := by
    intro d hd
    exact ⟨d, hd, rfl⟩
  constructor
  · exact not_hasAP_of_concrete_even_suspension
      k a m S (evenRaisedTypes S) A L R
      hA hL hR hAL hAR hcentral hraise
      (by rw [shiftedAllowed_evenRaisedTypes])
      hm hlow hNoLow
  · exact not_hasAP_of_concrete_even_suspension
      k a m S (Set.insert 0 (evenRaisedTypes S)) A L R
      hA hL hR hAL hAR hcentral
      (by intro d hd; exact (Set.mem_insert_iff).2 (Or.inr (hraise d hd)))
      (by rw [shiftedAllowed_evenRaisedTypes_insert_zero])
      hm hlow hNoLow

end Hypertournaments
