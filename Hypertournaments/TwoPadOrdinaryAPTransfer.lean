import Hypertournaments.CanonicalPadSide
import Hypertournaments.TwoPadJointReflection

/-!
# Conditional transfer of *ordinary* AP obstructions through two pads

This theorem packages all verified general reflection technology:
canonical padded one-point joint embeddings, preservation of source
orientations through arbitrary ambient embeddings (not merely strong
amalgams), pigeonhole on actual one-pad profiles, and the exact
shifted local-index formula.

The input left/right higher-arity source structures are assumed to be
admissible and to recover the old source orientations on every
two-pad tuple; proving these assumptions for even and rooted odd
suspensions is intentionally separate.

The contradiction applies to arbitrary ordinary higher-arity
amalgams, including attempts to identify the two new vertices. Such
identification is excluded by an explicit disagreement hypothesis on
the higher source orientations.

No unnamed AP axiom or reflection hypothesis is introduced.
-/

namespace Hypertournaments

/-- Source-side two-pad recovery, expressed in the canonical numbering
with m pads followed by a base of a vertices and a final new vertex. -/
def CanonicalTwoPadSideRecovery
    (n a m : ℕ)
    (L R : Hyper n (Fin (a + 1)))
    (BL BR : Hyper (n + 2) (Fin (m + a + 1))) : Prop :=
  (∀ (x y : Fin m) (hxy : x ≠ y)
      (t : Fin n ↪ Fin (a + 1)),
      BL.orient (twoPadSliceTuple
          (canonicalOldToSide m a)
          (canonicalPadToSide m a x) (canonicalPadToSide m a y)
          (canonicalPadToSide_not_mem_old m a x)
          (canonicalPadToSide_not_mem_old m a y)
          (fun he => hxy ((canonicalPadToSide m a).injective he))
          t) = L.orient t) ∧
  (∀ (x y : Fin m) (hxy : x ≠ y)
      (t : Fin n ↪ Fin (a + 1)),
      BR.orient (twoPadSliceTuple
          (canonicalOldToSide m a)
          (canonicalPadToSide m a x) (canonicalPadToSide m a y)
          (canonicalPadToSide_not_mem_old m a x)
          (canonicalPadToSide_not_mem_old m a y)
          (fun he => hxy ((canonicalPadToSide m a).injective he))
          t) = R.orient t)

/-- Actual higher source preservation gives the exact two-pad
recovery required by the profile pigeonhole lemma, on both sides
of the ordinary canonical joint. -/
theorem canonical_source_recovery_in_joint
    {n a m : ℕ}
    (L R : Hyper n (Fin (a + 1)))
    (BL BR : Hyper (n + 2) (Fin (m + a + 1)))
    (D : Hyper (n + 2) (Fin (m + a + 2)))
    (hBL : Preserves BL D (leftJointInclusion (m + a)))
    (hBR : Preserves BR D (rightJointInclusion (m + a)))
    (hrec : CanonicalTwoPadSideRecovery n a m L R BL BR) :
    RecoversOnePointSidesFromPads D
      (canonicalOldToJoint m a) (canonicalPadToJoint m a)
      (canonicalPadToJoint_not_mem_old m a) L R := by
  constructor
  · intro x y hlt hpq t
    have hxy : x ≠ y := ne_of_lt hlt
    have hside : canonicalPadToSide m a x ≠
        canonicalPadToSide m a y := by
      intro he
      exact hxy ((canonicalPadToSide m a).injective he)
    have hpad (z : Fin m) :
        leftJointInclusion (m + a) (canonicalPadToSide m a z) =
          canonicalPadToJoint m a z :=
      DFunLike.congr_fun (canonicalPad_left_commutes m a) z
    have hp' :
        leftJointInclusion (m + a) (canonicalPadToSide m a x) ∉
          Set.range (canonicalOldToJoint m a) := by
      rw [hpad x]
      exact canonicalPadToJoint_not_mem_old m a x
    have hq' :
        leftJointInclusion (m + a) (canonicalPadToSide m a y) ∉
          Set.range (canonicalOldToJoint m a) := by
      rw [hpad y]
      exact canonicalPadToJoint_not_mem_old m a y
    have hs :=
      twoPad_source_recovery_of_preserves
        L BL D
        (leftJointInclusion a) (canonicalOldToJoint m a)
        (canonicalOldToSide m a) (leftJointInclusion (m + a))
        (canonicalOld_left_commutes m a)
        (canonicalPadToSide m a x) (canonicalPadToSide m a y)
        (canonicalPadToSide_not_mem_old m a x)
        (canonicalPadToSide_not_mem_old m a y)
        hside hp' hq' hBL (hrec.1 x y hxy) t
    simpa only [hpad x, hpad y] using hs
  · intro x y hlt hpq t
    have hxy : x ≠ y := ne_of_lt hlt
    have hside : canonicalPadToSide m a x ≠
        canonicalPadToSide m a y := by
      intro he
      exact hxy ((canonicalPadToSide m a).injective he)
    have hpad (z : Fin m) :
        rightJointInclusion (m + a) (canonicalPadToSide m a z) =
          canonicalPadToJoint m a z :=
      DFunLike.congr_fun (canonicalPad_right_commutes m a) z
    have hp' :
        rightJointInclusion (m + a) (canonicalPadToSide m a x) ∉
          Set.range (canonicalOldToJoint m a) := by
      rw [hpad x]
      exact canonicalPadToJoint_not_mem_old m a x
    have hq' :
        rightJointInclusion (m + a) (canonicalPadToSide m a y) ∉
          Set.range (canonicalOldToJoint m a) := by
      rw [hpad y]
      exact canonicalPadToJoint_not_mem_old m a y
    have hs :=
      twoPad_source_recovery_of_preserves
        R BR D
        (rightJointInclusion a) (canonicalOldToJoint m a)
        (canonicalOldToSide m a) (rightJointInclusion (m + a))
        (canonicalOld_right_commutes m a)
        (canonicalPadToSide m a x) (canonicalPadToSide m a y)
        (canonicalPadToSide_not_mem_old m a x)
        (canonicalPadToSide_not_mem_old m a y)
        hside hp' hq' hBR (hrec.2 x y hxy) t
    simpa only [hpad x, hpad y] using hs

/-- If the lower-arity sides have no canonical ordinary joint, then
the corresponding higher-arity sides cannot have such a joint,
provided the construction really recovers the lower source signs.
This step uses the actual available pads and their profile equality,
not an abstract existence assumption about a recovered slice. -/
theorem no_canonical_high_joint_of_twoPad_recovery
    {n a m : ℕ} (S T : Set ℕ)
    (L R : Hyper n (Fin (a + 1)))
    (BL BR : Hyper (n + 2) (Fin (m + a + 1)))
    (hNoLow : ∀ E : Hyper n (Fin (a + 2)),
        Admissible S E →
        Preserves L E (leftJointInclusion a) →
        Preserves R E (rightJointInclusion a) → False)
    (hshift : shiftedAllowed T ⊆ S)
    (hm : 2 ^ Fintype.card (Fin (n + 1) ↪ Fin (a + 2)) < m)
    (hrec : CanonicalTwoPadSideRecovery n a m L R BL BR)
    (D : Hyper (n + 2) (Fin (m + a + 2)))
    (hD : Admissible T D)
    (hBL : Preserves BL D (leftJointInclusion (m + a)))
    (hBR : Preserves BR D (rightJointInclusion (m + a))) :
    False := by
  exact no_higher_joint_of_many_pads_and_recovery
    S T L R hNoLow D (canonicalOldToJoint m a)
    (canonicalPadToJoint m a)
    (canonicalPadToJoint_not_mem_old m a)
    hD hshift hm
    (canonical_source_recovery_in_joint L R BL BR D hBL hBR hrec)

/-- Fully ordinary non-AP transfer, conditional only on an explicitly
specified admissible padded one-point span and its exact two-pad
source recovery. An arbitrary high-amalgam identification is eliminated
using the actual high-side orientation disagreement. -/
theorem not_hasAP_of_canonical_twoPad_lift
    {n a m : ℕ} (S T : Set ℕ)
    (L R : Hyper n (Fin (a + 1)))
    (Ahi : Hyper (n + 2) (Fin (m + a)))
    (BL BR : Hyper (n + 2) (Fin (m + a + 1)))
    (hAhi : Admissible T Ahi)
    (hBLad : Admissible T BL) (hBRad : Admissible T BR)
    (hAL : Preserves Ahi BL (onePointBaseEmbedding (m + a)))
    (hAR : Preserves Ahi BR (onePointBaseEmbedding (m + a)))
    (hdisagree : ∃ t : Fin (n + 2) ↪ Fin (m + a + 1),
        BL.orient t ≠ BR.orient t)
    (hNoLow : ∀ E : Hyper n (Fin (a + 2)),
        Admissible S E →
        Preserves L E (leftJointInclusion a) →
        Preserves R E (rightJointInclusion a) → False)
    (hshift : shiftedAllowed T ⊆ S)
    (hm : 2 ^ Fintype.card (Fin (n + 1) ↪ Fin (a + 2)) < m)
    (hrec : CanonicalTwoPadSideRecovery n a m L R BL BR) :
    ¬ HasAP (n + 2) T := by
  apply not_hasAP_of_no_joint Ahi BL BR hAhi hBLad hBRad
    hAL hAR hdisagree
  intro D hD hDL hDR
  exact no_canonical_high_joint_of_twoPad_recovery
    S T L R BL BR hNoLow hshift hm hrec D hD hDL hDR

end Hypertournaments
