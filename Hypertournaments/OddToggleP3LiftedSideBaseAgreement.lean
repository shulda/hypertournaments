import Mathlib.Tactic.Ext
import Hypertournaments.OddToggleP3LiftedSideLinks
import Hypertournaments.OddToggleP3BasePreservation
import Hypertournaments.OnePointJoint

/-!
# Two lifted p3 side potentials agree on the true common old base

Use canonical p3 one-point side potentials with all m*t old vertices
first and fresh vertex Fin.last (m*t), and two arbitrary, possibly
different eligible missing-block halves and new-link tables L,R.

Let the two sides embed injectively into an arbitrary common ambient
finite joint, with old vertex inclusions agreeing on every old point.
Lift the TWO side potentials along their respective embeddings by the
finite preimage operation. Then their lifted values on EVERY image
of an old finite subset agree exactly, since both equal the original
W-induced full-transversal base potential there.

This discharges, without a probability assumption, the actual
old-base cochain agreement hypothesis of the all-genuine-joints p3
mixed gauge theorem. The endpoint link and order hypotheses remain
separate.
-/

namespace Hypertournaments

/-- Finset image commutes exactly with a commuting diagram of
injective vertex maps; no order-preserving premise is required. -/
theorem p3Finset_image_commutes
    {A B C : Type*} [DecidableEq B] [DecidableEq C]
    (f : A ↪ B) (g : B ↪ C) (h : A ↪ C)
    (hcomm : ∀ v : A, g (f v) = h v)
    (Q : Finset A) :
    (Q.image f).image g = Q.image h := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨u, hu, hux⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, hvu⟩ := Finset.mem_image.mp hu
    refine Finset.mem_image.mpr ⟨v, hv, ?_⟩
    calc
      h v = g (f v) := (hcomm v).symm
      _ = g u := congrArg g hvu
      _ = x := hux
  · intro hx
    obtain ⟨v, hv, hvx⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr
      ⟨f v, Finset.mem_image.mpr ⟨v, hv, rfl⟩, ?_⟩
    exact (hcomm v).trans hvx

/-- The two arbitrary genuine side potential tables, lifted along
two arbitrary injections into a joint and agreeing on the old base
vertex images, remain equal on ALL actual images of old finite
subsets. They both coincide there with the same W base potential. -/
theorem p3CanonicalLiftedSides_agree_old_base
    (m t : ℕ)
    (eligibleL eligibleR : Finset (Fin m))
    (W L R : Finset (Fin (m*t)) → ZMod 2)
    (gL gR : Fin (m*t+1) ↪ Fin (m*t+2))
    (oldJoint : Fin (m*t) ↪ Fin (m*t+2))
    (hL : ∀ v : Fin (m*t),
      gL ((onePointBaseEmbedding (m*t)) v) = oldJoint v)
    (hR : ∀ v : Fin (m*t),
      gR ((onePointBaseEmbedding (m*t)) v) = oldJoint v)
    (Q : Finset (Fin (m*t))) :
    p3LiftFinPotential gL
      (p3SidePotential m t (onePointBaseEmbedding (m*t))
        (Fin.last (m*t)) eligibleL W L)
      (Q.image oldJoint) =
    p3LiftFinPotential gR
      (p3SidePotential m t (onePointBaseEmbedding (m*t))
        (Fin.last (m*t)) eligibleR W R)
      (Q.image oldJoint) := by
  let old : Fin (m*t) ↪ Fin (m*t+1) := onePointBaseEmbedding (m*t)
  let fresh : Fin (m*t+1) := Fin.last (m*t)
  let zL := p3SidePotential m t old fresh eligibleL W L
  let zR := p3SidePotential m t old fresh eligibleR W R
  have hfresh : ∀ v : Fin (m*t), old v ≠ fresh := by
    intro v
    exact Fin.castSucc_ne_last v
  have himageL : (Q.image old).image gL = Q.image oldJoint :=
    p3Finset_image_commutes old gL oldJoint hL Q
  have himageR : (Q.image old).image gR = Q.image oldJoint :=
    p3Finset_image_commutes old gR oldJoint hR Q
  change p3LiftFinPotential gL zL (Q.image oldJoint) =
    p3LiftFinPotential gR zR (Q.image oldJoint)
  calc
    p3LiftFinPotential gL zL (Q.image oldJoint) =
        p3LiftFinPotential gL zL ((Q.image old).image gL) := by
          rw [himageL]
    _ = zL (Q.image old) :=
      p3LiftFinPotential_image gL zL (Q.image old)
    _ = p3BasePotential m t W Q :=
      p3SidePotential_image_old_base m t old fresh
        hfresh eligibleL W L Q
    _ = zR (Q.image old) :=
      (p3SidePotential_image_old_base m t old fresh
        hfresh eligibleR W R Q).symm
    _ = p3LiftFinPotential gR zR ((Q.image old).image gR) :=
      (p3LiftFinPotential_image gR zR (Q.image old)).symm
    _ = p3LiftFinPotential gR zR (Q.image oldJoint) := by
      rw [himageR]

end Hypertournaments
