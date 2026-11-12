import Hypertournaments.OddToggleP3ActualJointParity
import Hypertournaments.OddToggleP3MixedGaugeAssembly

/-!
# Every actual parity-respecting p3 joint has the required mixed gauge

For any actual intrinsic arity n=4k+3 switching hypertournament
joint E on Fin(a+2), with an injective old base and two distinct
fresh vertices, the genuine canonical mixed cochain x satisfies
δx = alpha+beta on every old m-set, m=n−1=4k+2.

If the prescribed left/right side link sum is δh on the old base,
the already proved full-simplex cone contraction gives an actual
lower cochain u with x=h+δu on EVERY old (m−1)-set.

The proof does not choose any preferred mixed completion. It
quantifies over all genuine switching joints E, and the only
extra premise is the exact side-link identity to the supplied h.
A root of the old base is explicit (no hidden nonempty assumption).

This is the intended converse gauge statement in intrinsic
hypertournament geometry. It is still conditional on links
matching the concrete admissible side potentials, and does not
by itself prove a random nonamalgamation obstruction.
-/

namespace Hypertournaments

/-- Full genuine p3 joint gauge: every switching-admissible
hypothetical E extending side links whose sum is δh has its
entire mixed orientation cochain equal to h+δu. -/
theorem Hyper.p3ActualJoint_has_mixed_gauge
    (k a : ℕ) (root : Fin a)
    (E : Hyper (4*k+3) (Fin (a+2)))
    (hE : Admissible (switchingAllowed (4*k+3)) E)
    (old : Fin a ↪ Fin (a+2))
    (l r : Fin (a+2)) (hlr : l ≠ r)
    (hFresh : ∀ v : Fin a, old v ≠ l ∧ old v ≠ r)
    (h : Finset (Fin a) → ZMod 2)
    (hlink : ∀ Q : Finset (Fin a), Q.card = 4*k+2 →
      p1BitToZMod (E.canonicalSignTable (insert l (Q.image old))) +
      p1BitToZMod (E.canonicalSignTable (insert r (Q.image old))) =
      coboundary h Q) :
    ∃ u : Finset (Fin a) → ZMod 2,
      ∀ U : Finset (Fin a), U.card = 4*k+1 →
        contractAt r
          (contractAt l
            (fun T : Finset (Fin (a+2)) =>
              p1BitToZMod (E.canonicalSignTable T)))
          (U.image old) =
        h U + coboundary u U := by
  let e : Finset (Fin (a+2)) → ZMod 2 :=
    fun T => p1BitToZMod (E.canonicalSignTable T)
  let x : Finset (Fin a) → ZMod 2 :=
    fun U => contractAt r (contractAt l e) (U.image old)
  let alpha : Finset (Fin a) → ZMod 2 :=
    fun Q => e (insert l (Q.image old))
  let beta : Finset (Fin a) → ZMod 2 :=
    fun Q => e (insert r (Q.image old))
  have hmixed : ∀ Q : Finset (Fin a), Q.card = 4*k+2 →
      coboundary x Q = alpha Q + beta Q := by
    intro Q hQ
    exact Hyper.p3ActualJoint_mixedParity
      k a E hE old l r hlr hFresh Q hQ
  have hlinks : ∀ Q : Finset (Fin a), Q.card = 4*k+2 →
      alpha Q + beta Q = coboundary h Q := by
    intro Q hQ
    exact hlink Q hQ
  obtain ⟨u, hu⟩ :=
    p3MixedGauge_of_link_parity root (4*k+2) (by omega)
      alpha beta h x hlinks hmixed
  refine ⟨u, ?_⟩
  intro U hU
  exact hu U (by omega)

end Hypertournaments
