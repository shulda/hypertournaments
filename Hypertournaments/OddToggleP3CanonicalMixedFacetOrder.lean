import Hypertournaments.OddToggleP3BoolPhases

/-!
# Correct raw mixed packet facet order in the canonical p3 joint

The mathematical working note used the auxiliary order l < A < r,
but the intrinsic ordinary-AP canonical joint represents
the OLD base first, then fresh left l, then fresh right r.

Hence the raw facets in the increasing mixed packet are
  (x_0, ..., x_{m-1}, beta(Q), alpha(Q)),
where beta deletes left and alpha deletes right.
It is NOT the older display (beta,x_0,...,alpha).

For m even, if the whole packet is alternating with initial phase b,
the last two endpoints must satisfy beta=b and alpha=!b. This
order distinction must be used in the eventual actual-joint
event identification; it does not change the two-pattern count.
-/

namespace Hypertournaments

/-- Concatenate the m mixed facets with the right-side link
beta (delete left fresh) and left-side link alpha (delete right).
This is the actual canonical joint's increasing facet order. -/
def p3CanonicalMixedRawWord (m : ℕ)
    (interior : Fin m → Bool) (beta alpha : Bool) :
    Fin (m+2) → Bool :=
  Fin.snoc (Fin.snoc interior beta) alpha

/-- The first m positions of the canonical mixed facet packet
are exactly the m ordered mixed facets. -/
theorem p3CanonicalMixedRawWord_interior
    (m : ℕ) (interior : Fin m → Bool) (beta alpha : Bool)
    (i : Fin m) :
    p3CanonicalMixedRawWord m interior beta alpha
      i.castSucc.castSucc = interior i := by
  simp [p3CanonicalMixedRawWord]

/-- The second-to-last facet deletes the left fresh point,
so this is the right-side link beta. -/
theorem p3CanonicalMixedRawWord_beta
    (m : ℕ) (interior : Fin m → Bool) (beta alpha : Bool) :
    p3CanonicalMixedRawWord m interior beta alpha
      (Fin.last m).castSucc = beta := by
  simp [p3CanonicalMixedRawWord]

/-- The last facet deletes the right fresh point,
so this is the left-side link alpha. -/
theorem p3CanonicalMixedRawWord_alpha
    (m : ℕ) (interior : Fin m → Bool) (beta alpha : Bool) :
    p3CanonicalMixedRawWord m interior beta alpha
      (Fin.last (m+1)) = alpha := by
  simp [p3CanonicalMixedRawWord]

/-- For even m, every alternating canonical mixed packet has
right-side endpoint beta equal to its initial phase and
left-side endpoint alpha equal to the opposite phase. -/
theorem p3CanonicalMixedRawWord_alternating_endpoints
    (m : ℕ) (hm : m%2=0)
    (interior : Fin m → Bool) (beta alpha phase : Bool)
    (hword : p3CanonicalMixedRawWord m interior beta alpha =
      p3AlternatingWord (m+2) phase) :
    beta = phase ∧ alpha = !phase := by
  have hb := congrFun hword ((Fin.last m).castSucc)
  have ha := congrFun hword (Fin.last (m+1))
  have hEven : ((Fin.last m).castSucc : Fin (m+2)).val%2=0 := by
    simpa using hm
  have hOdd : (Fin.last (m+1) : Fin (m+2)).val%2=1 := by
    change (m+1)%2=1
    omega
  constructor
  · rw [p3CanonicalMixedRawWord_beta] at hb
    simpa [p3AlternatingWord, hEven] using hb
  · rw [p3CanonicalMixedRawWord_alpha] at ha
    simpa [p3AlternatingWord, hOdd] using ha

end Hypertournaments
