import Hypertournaments.AllArityCanonicalAdmissibility
import Hypertournaments.EvenSuspensionAllTwoPadPackets
import Hypertournaments.EvenSuspensionIncreasingCentralFar
import Hypertournaments.EvenSuspensionIncreasingCentralThree

/-!
# Full intrinsic age membership for the even two-coordinate suspension

Let n=2k. For every old n-hypertournament whose local indices are in
S, if the central old index k belongs to S, the concrete even
two-coordinate suspension has all local indices in
S^{+} = {d+1 : d in S}.

Proof, in the actual intrinsic language:
* canonical certification reduces arbitrary enumerations to increasing
  tuples (general local-index permutation invariance);
* 0,1 or >=4 pad packets have high type k+1;
* exactly three-pad packets have high type k+1;
* exactly two-pad packets have high type d+1 for an actual old
  (n+1)-tuple with old type d in S.

The result is unconditional; it is the construction-specific
admissibility hypothesis needed for even-arity ordinary AP reflection.
Source recovery and common-base preservation are separate,
previously proved statements.
-/

namespace Hypertournaments

/-- Exact shifted family of old local-type indices. -/
def evenRaisedTypes (S : Set ℕ) : Set ℕ :=
  {d | ∃ e : ℕ, e ∈ S ∧ d = e + 1}

/-- The explicit even suspension preserves age membership under
the exact +1 shift, provided the old central type is allowed. -/
theorem Hyper.evenSuspension_admissible
    (k m a : ℕ) (S : Set ℕ)
    (A : Hyper (2 * k) (Fin a))
    (hA : Admissible S A) (hcentral : k ∈ S) :
    Admissible (evenRaisedTypes S) (A.evenSuspension m a) := by
  apply (admissible_iff_canonical_all
    (evenRaisedTypes S) (A.evenSuspension m a)).2
  intro Q hQ
  let f : Fin (2 * k + 3) ↪o Fin (m + a) := Q.orderEmbOfFin hQ
  change localIndex (A.evenSuspension m a) f.toEmbedding ∈
    evenRaisedTypes S
  change ∃ e : ℕ, e ∈ S ∧
    localIndex (A.evenSuspension m a) f.toEmbedding = e + 1
  by_cases hfar :
      (evenPadProjection m a (tupleVertices f.toEmbedding)).card ≤ 1 ∨
      4 ≤ (evenPadProjection m a (tupleVertices f.toEmbedding)).card
  · have hindex :=
      A.evenSuspension_localIndex_increasing_far k m a f hfar
    exact ⟨k, hcentral, hindex⟩
  · by_cases htwo :
        (evenPadProjection m a (tupleVertices f.toEmbedding)).card = 2
    · obtain ⟨t, hindex⟩ :=
        A.evenSuspension_localIndex_increasing_twoPads m a f htwo
      exact ⟨localIndex A t.toEmbedding, hA t.toEmbedding, hindex⟩
    · have hthree :
          (evenPadProjection m a (tupleVertices f.toEmbedding)).card = 3 := by
        have hlow :
            2 ≤ (evenPadProjection m a
              (tupleVertices f.toEmbedding)).card := by
          by_contra hh
          exact hfar (Or.inl (by omega))
        have hhigh :
            (evenPadProjection m a
              (tupleVertices f.toEmbedding)).card ≤ 3 := by
          by_contra hh
          exact hfar (Or.inr (by omega))
        omega
      have hindex :=
        A.evenSuspension_localIndex_increasing_threePads k m a f hthree
      exact ⟨k, hcentral, hindex⟩

/-- Any high allowed family containing every shifted old index
admits the concrete even suspension. This is the form needed for
the ordinary amalgamation obstruction transfer. -/
theorem Hyper.evenSuspension_admissible_of_shift
    (k m a : ℕ) (S T : Set ℕ)
    (A : Hyper (2 * k) (Fin a))
    (hA : Admissible S A)
    (hcentral : k ∈ S)
    (hshift : ∀ d : ℕ, d ∈ S → d + 1 ∈ T) :
    Admissible T (A.evenSuspension m a) := by
  apply admissible_mono (T := T) ?_
    (A.evenSuspension_admissible k m a S hA hcentral)
  intro d hd
  obtain ⟨e, he, hde⟩ := hd
  rw [hde]
  exact hshift e he

end Hypertournaments
