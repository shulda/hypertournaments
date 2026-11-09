import Hypertournaments.RootedOddThreePadAbsentLocalIndex
import Hypertournaments.RootedOddThreePadRootZero
import Hypertournaments.RootedOddFarCentral
import Hypertournaments.RootedOddFourPadLocalIndex
import Hypertournaments.RootedOddTwoPadShift
import Hypertournaments.AllArityCanonicalAdmissibility
import Hypertournaments.EvenSuspensionAdmissibility

/-!
# Full intrinsic age membership for the rooted odd suspension

For an odd old arity 2k+1 and canonical least root r=0, the concrete
two-coordinate rooted suspension preserves admissibility after shifting
all old local indices by +1, as long as the old central index k+1 is
allowed.

The complete local packet case distinction is:
* h <= 1 or h >= 5 pads: central index k+2;
* h = 2 pads: actual old local index +1;
* h = 3 pads with root present: central index k+2;
* h = 3 pads without root: actual old local index +1;
* h = 4 pads: central index k+2.

The least-root condition is used only for the root-present h=3 case:
it forces the root into the first old position of an increasing packet.
The other sign-table and index-shift lemmas do not assume admissibility.

The proof is about ordinary intrinsic hypertournaments; the increasing
tuple is only used for the canonical packet verification. All arbitrary
tuple orders are covered by the pre-existing permutation invariance.
-/

namespace Hypertournaments

/-- The canonical-root odd suspension maps every S-admissible old
hypertournament of odd arity 2k+1 to an admissible higher hypertournament
with precisely the successor family of old allowed types. -/
theorem Hyper.rootedOddSuspension_admissible
    (k m a : ℕ) (S : Set ℕ)
    (A : Hyper (2*k+1) (Fin a))
    (root : Fin a) (hroot0 : root.val = 0)
    (hA : Admissible S A) (hcentral : k+1 ∈ S) :
    Admissible (evenRaisedTypes S) (A.rootedOddSuspension m a root) := by
  apply (admissible_iff_canonical_all
    (evenRaisedTypes S) (A.rootedOddSuspension m a root)).2
  intro Q hQ
  let f : Fin (2*k+4) ↪o Fin (m+a) := Q.orderEmbOfFin hQ
  change localIndex (A.rootedOddSuspension m a root) f.toEmbedding ∈
    evenRaisedTypes S
  change ∃ e : ℕ, e ∈ S ∧
    localIndex (A.rootedOddSuspension m a root) f.toEmbedding = e+1
  let p : ℕ :=
    (evenPadProjection m a (tupleVertices f.toEmbedding)).card
  by_cases hfar : p ≤ 1 ∨ 5 ≤ p
  · have hidx :=
      A.rootedOddSuspension_localIndex_increasing_far k m a root f hfar
    refine ⟨k+1, hcentral, ?_⟩
    omega
  · by_cases htwo : p = 2
    · obtain ⟨t, ht⟩ :=
        A.rootedOddSuspension_localIndex_increasing_twoPads
          m a root f htwo
      exact ⟨localIndex A t.toEmbedding, hA t.toEmbedding, ht⟩
    · by_cases hthree : p = 3
      · by_cases hroot :
          root ∈ evenOldProjection m a (tupleVertices f.toEmbedding)
        · have hidx :=
            A.rootedOddSuspension_localIndex_threePads_rootZero_present
              k m a root hroot0 f hthree hroot
          refine ⟨k+1, hcentral, ?_⟩
          omega
        · obtain ⟨t, ht⟩ :=
            A.rootedOddSuspension_localIndex_threePads_rootZero_absent
              k m a root hroot0 f hthree hroot
          exact ⟨localIndex A t.toEmbedding, hA t.toEmbedding, ht⟩
      · have hfour : p = 4 := by omega
        have hidx :=
          A.rootedOddSuspension_localIndex_increasing_fourPads
            k m a root f hfour
        refine ⟨k+1, hcentral, ?_⟩
        omega

/-- A target allowed family containing every shifted old type
admits the concrete rooted odd suspension. -/
theorem Hyper.rootedOddSuspension_admissible_of_shift
    (k m a : ℕ) (S T : Set ℕ)
    (A : Hyper (2*k+1) (Fin a))
    (root : Fin a) (hroot0 : root.val = 0)
    (hA : Admissible S A)
    (hcentral : k+1 ∈ S)
    (hshift : ∀ d : ℕ, d ∈ S → d+1 ∈ T) :
    Admissible T (A.rootedOddSuspension m a root) := by
  apply admissible_mono (T := T) ?_
    (A.rootedOddSuspension_admissible k m a S root hroot0 hA hcentral)
  intro d hd
  obtain ⟨e, he, hde⟩ := hd
  rw [hde]
  exact hshift e he

end Hypertournaments
