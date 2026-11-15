import Lean.Elab.Tactic.Omega
import Hypertournaments.LocalForbiddenFamily
import Hypertournaments.PairAmalgamation
import Hypertournaments.EvenAmalgamation
import Hypertournaments.NegativeClassification

/-!
# Positive local-index classes and the exact AP classification

Source: `tex_hypertournaments` at
`919349e7eceed3c7fa0ed126a337c6fae6624704`.

If the central and next-central packet types are allowed, every forbidden
packet is pair-cancelling. The existing same-carrier completion therefore
gives strong amalgamation of the actual admissible class. Together with
the switching construction, this proves both positive alternatives and
closes the ordinary-AP classification against the shared negative theorem.
-/

namespace Hypertournaments

/-- Both central types suffice for strong amalgamation of the genuine
local-index class, with exactly the prescribed overlap and no extra vertices. -/
theorem central_next_strong_span {n : ℕ} (hn : 3 ≤ n)
    (S : Set ℕ) (hcentral : centralIndex n ∈ S) (hnext : nextCentralIndex n ∈ S)
    {A B C : Type*} [Finite B] [Finite C]
    (AA : Hyper n A) (BB : Hyper n B) (CC : Hyper n C)
    (f : A ↪ B) (g : A ↪ C) (hAB : Preserves AA BB f) (hAC : Preserves AA CC g)
    (hB : Admissible S BB) (hC : Admissible S CC) :
    ∃ D : Hyper n (FiniteStrongSpan.Carrier f g),
      Admissible S D ∧ Preserves BB D (FiniteStrongSpan.left f g) ∧
        Preserves CC D (FiniteStrongSpan.right f g) := by
  obtain ⟨D, hD, hi, hj⟩ := pair_cancelling_strong_span hn (localForbiddenFamily n S)
    (localForbiddenFamily_pairCancelling hn S hcentral hnext) AA BB CC f g hAB hAC
    ((omits_localForbiddenFamily_iff_admissible S BB).mpr hB)
    ((omits_localForbiddenFamily_iff_admissible S CC).mpr hC)
  exact ⟨D, (omits_localForbiddenFamily_iff_admissible S D).mp hD, hi, hj⟩

/-- Free compatible vertex orders can also be preserved on this same strong
amalgam carrier. The order is additional data, not part of `Preserves`. -/
theorem central_next_ordered_strong_span {n : ℕ} (hn : 3 ≤ n)
    (S : Set ℕ) (hcentral : centralIndex n ∈ S) (hnext : nextCentralIndex n ∈ S)
    {A B C : Type*} [Finite A] [Finite B] [Finite C]
    [LinearOrder A] [LinearOrder B] [LinearOrder C]
    (AA : Hyper n A) (BB : Hyper n B) (CC : Hyper n C)
    (f : A ↪o B) (g : A ↪o C)
    (hAB : Preserves AA BB f.toEmbedding) (hAC : Preserves AA CC g.toEmbedding)
    (hB : Admissible S BB) (hC : Admissible S CC) :
    ∃ (order : LinearOrder (FiniteStrongSpan.Carrier f.toEmbedding g.toEmbedding))
      (D : Hyper n (FiniteStrongSpan.Carrier f.toEmbedding g.toEmbedding)),
      Admissible S D ∧ Preserves BB D (FiniteStrongSpan.left f.toEmbedding g.toEmbedding) ∧
      Preserves CC D (FiniteStrongSpan.right f.toEmbedding g.toEmbedding) ∧
      (∀ x y : B, x < y → @LT.lt _ order.toLT
        (FiniteStrongSpan.left f.toEmbedding g.toEmbedding x)
        (FiniteStrongSpan.left f.toEmbedding g.toEmbedding y)) ∧
      (∀ x y : C, x < y → @LT.lt _ order.toLT
        (FiniteStrongSpan.right f.toEmbedding g.toEmbedding x)
        (FiniteStrongSpan.right f.toEmbedding g.toEmbedding y)) := by
  obtain ⟨order, D, hD, hi, hj, hiOrder, hjOrder⟩ := pair_cancelling_ordered_strong_span hn
    (localForbiddenFamily n S) (localForbiddenFamily_pairCancelling hn S hcentral hnext)
    AA BB CC f g hAB hAC
    ((omits_localForbiddenFamily_iff_admissible S BB).mpr hB)
    ((omits_localForbiddenFamily_iff_admissible S CC).mpr hC)
  exact ⟨order, D, (omits_localForbiddenFamily_iff_admissible S D).mp hD,
    hi, hj, hiOrder, hjOrder⟩

/-- The finite forbidden-family SAP interface now concerns exactly the
admissible local-index class, rather than a separate conditional reduction. -/
theorem central_next_hasStrongAmalgamation {n : ℕ} (hn : 3 ≤ n)
    (S : Set ℕ) (hcentral : centralIndex n ∈ S) (hnext : nextCentralIndex n ∈ S) :
    HasStrongAmalgamation (localForbiddenFamily n S) :=
  pair_cancelling_hasStrongAmalgamation hn (localForbiddenFamily n S)
    (localForbiddenFamily_pairCancelling hn S hcentral hnext)

/-- Positive ordinary AP when the central and next-central types are allowed,
using the original `HasAP` interface without an order-preservation premise. -/
theorem central_next_hasAP (n : ℕ) (hn : 3 ≤ n)
    (S : Set ℕ) (hcentral : centralIndex n ∈ S) (hnext : nextCentralIndex n ∈ S) :
    HasAP n S := by
  intro a b c A B C hA hB hC f g hAB hAC
  obtain ⟨d, D, i, j, hD, hi, hj, hcomm, _hoverlap⟩ :=
    central_next_hasStrongAmalgamation hn S hcentral hnext a b c A B C
      ((omits_localForbiddenFamily_iff_admissible S A).mpr hA)
      ((omits_localForbiddenFamily_iff_admissible S B).mpr hB)
      ((omits_localForbiddenFamily_iff_admissible S C).mpr hC) f g hAB hAC
  exact ⟨d, D, i, j, (omits_localForbiddenFamily_iff_admissible S D).mp hD,
    hi, hj, hcomm⟩

/-- Both alternatives in the ordinary-AP classification actually have strong
amalgamation. This statement includes the exceptional switching alternative. -/
theorem positive_classification_strong_span {n : ℕ} (hn : 4 ≤ n)
    (S : Set ℕ) (hcentral : centralIndex n ∈ S) (halternatives : NecessaryAlternatives n S)
    {A B C : Type*} [Finite B] [Finite C]
    (AA : Hyper n A) (BB : Hyper n B) (CC : Hyper n C)
    (f : A ↪ B) (g : A ↪ C) (hAB : Preserves AA BB f) (hAC : Preserves AA CC g)
    (hB : Admissible S BB) (hC : Admissible S CC) :
    ∃ D : Hyper n (FiniteStrongSpan.Carrier f g),
      Admissible S D ∧ Preserves BB D (FiniteStrongSpan.left f g) ∧
        Preserves CC D (FiniteStrongSpan.right f g) := by
  rcases halternatives with hnext | ⟨hodd, rfl⟩
  · exact central_next_strong_span (by omega) S hcentral hnext AA BB CC f g hAB hAC hB hC
  · exact switching_strong_span hodd (by omega) AA BB CC f g hAB hAC hB hC

/-- The sufficient direction of the local-index AP classification. It needs
no restriction on phantom indices beyond the displayed positive alternative. -/
theorem positive_classification (n : ℕ) (hn : 4 ≤ n)
    (S : Set ℕ) (hcentral : centralIndex n ∈ S)
    (halternatives : NecessaryAlternatives n S) : HasAP n S := by
  rcases halternatives with hnext | ⟨hodd, rfl⟩
  · exact central_next_hasAP n (by omega) S hcentral hnext
  · exact switching_hasAP n hodd (by omega)

/-- Exact ordinary-amalgamation classification in every arity at least four,
under the same explicit validity and central-type premises as the negative
theorem. Both positive alternatives have been fully discharged. -/
theorem amalgamation_classification (n : ℕ) (hn : 4 ≤ n)
    (S : Set ℕ) (hvalid : ValidTypes n S) (hcentral : centralIndex n ∈ S) :
    HasAP n S ↔ NecessaryAlternatives n S := by
  constructor
  · exact negative_classification n hn S hvalid hcentral
  · exact positive_classification n hn S hcentral

/-- In the classified central-type setting, ordinary AP already supplies a
strong amalgam for every finite span of the actual admissible structures. -/
theorem strong_span_of_hasAP {n : ℕ} (hn : 4 ≤ n)
    (S : Set ℕ) (hvalid : ValidTypes n S) (hcentral : centralIndex n ∈ S)
    (hAP : HasAP n S)
    {A B C : Type*} [Finite B] [Finite C]
    (AA : Hyper n A) (BB : Hyper n B) (CC : Hyper n C)
    (f : A ↪ B) (g : A ↪ C) (hAB : Preserves AA BB f) (hAC : Preserves AA CC g)
    (hB : Admissible S BB) (hC : Admissible S CC) :
    ∃ D : Hyper n (FiniteStrongSpan.Carrier f g),
      Admissible S D ∧ Preserves BB D (FiniteStrongSpan.left f g) ∧
        Preserves CC D (FiniteStrongSpan.right f g) :=
  positive_classification_strong_span hn S hcentral
    (negative_classification n hn S hvalid hcentral hAP) AA BB CC f g hAB hAC hB hC

end Hypertournaments
