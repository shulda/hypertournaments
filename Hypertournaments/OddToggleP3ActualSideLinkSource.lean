import Mathlib.Tactic.Ext
import Hypertournaments.OddToggleP3CanonicalSides
import Hypertournaments.OddToggleP3CochainSideLinks
import Hypertournaments.OddToggleP3GenuineSideLinkTransfer

/-!
# Actual p3 canonical one-point endpoint link in terms of W and L

On a true old full block-transversal Q (m old vertices), the
canonical orientation of the (m+1)-set Q∪{fresh} in the actual
potential-induced one-point side is the F₂ sum
  W(Q) + δL_eligible(Q).
Here L_eligible(U)=L(U) if U is an eligible one-block-missing
transversal, and is zero otherwise. Crucially this is the same
side potential used in the genuine intrinsic Hyper structure,
not an abstract redefinition of the link orientation.

The full-transversal W bit and all punctured eligible link bits
are thus separated at the level of true canonical orientations.
Future work will identify Q with the real zero-sum coordinate
code and use this identity for both joint endpoints and fresh
identification events.
-/

namespace Hypertournaments

open scoped Classical

/-- The actual canonical one-fresh potential, on a set with new
vertex and an old-only embedded set U, is the eligible missing-
block L coefficient and never a W coefficient. -/
theorem p3CanonicalSidePotential_fresh_old_image
    (m t : ℕ)
    (eligible : Finset (Fin m))
    (W L : Finset (Fin (m*t)) → ZMod 2)
    (U : Finset (Fin (m*t))) :
    p3SidePotential m t
      (onePointBaseEmbedding (m*t)) (Fin.last (m*t)) eligible W L
      (insert (Fin.last (m*t))
        (U.image (onePointBaseEmbedding (m*t)))) =
    if p3IsEligibleMissingTransversal m t eligible U then L U else 0 := by
  classical
  let a := m*t
  let old : Fin a ↪ Fin (a+1) := onePointBaseEmbedding a
  let fresh : Fin (a+1) := Fin.last a
  have hpart : p3SideOldPart old
      (insert fresh (U.image old)) = U := by
    calc
      p3SideOldPart old (insert fresh (U.image old)) =
          p3SideOldPart old (U.image old) := by
            ext v
            simp only [p3SideOldPart, Finset.mem_filter,
              Finset.mem_univ, true_and]
            have hn : old v ≠ fresh := Fin.castSucc_ne_last v
            simp [hn]
      _ = U := p3SideOldPart_image m t old U
  change (if fresh ∈ insert fresh (U.image old)
    then (if p3IsEligibleMissingTransversal m t eligible
      (p3SideOldPart old (insert fresh (U.image old)))
      then L (p3SideOldPart old (insert fresh (U.image old)))
      else 0)
    else if p3IsBlockTransversal m t
      (p3SideOldPart old (insert fresh (U.image old)))
      then W (p3SideOldPart old (insert fresh (U.image old)))
      else 0) =
    (if p3IsEligibleMissingTransversal m t eligible U then L U else 0)
  simp [hpart]

/-- On every genuine old m-element FULL block-transversal Q,
the side's TRUE canonical endpoint sign is the independent
W(Q) bit plus the coboundary of the eligible punctured L table.
This is the exact source-variable formula needed for p3 random
non-amalgamation. -/
theorem p3CanonicalSide_link_on_full_transversal
    (m t : ℕ) (eligible : Finset (Fin m))
    (W L : Finset (Fin (m*t)) → ZMod 2)
    (Q : Finset (Fin (m*t)))
    (hQ : p3IsBlockTransversal m t Q) :
    p1BitToZMod
      ((p3CanonicalSide m t eligible W L).canonicalSignTable
        (insert (Fin.last (m*t))
          (Q.image (onePointBaseEmbedding (m*t))))) =
      W Q +
      coboundary
        (fun U : Finset (Fin (m*t)) =>
          if p3IsEligibleMissingTransversal m t eligible U
          then L U else 0) Q := by
  classical
  let a := m*t
  let old : Fin a ↪ Fin (a+1) := onePointBaseEmbedding a
  let fresh : Fin (a+1) := Fin.last a
  let z : Finset (Fin (a+1)) → ZMod 2 :=
    p3SidePotential m t old fresh eligible W L
  let link : Finset (Fin a) → ZMod 2 :=
    fun U => if p3IsEligibleMissingTransversal m t eligible U
      then L U else 0
  have hOldCard : (Q.image old).card = m := by
    rw [Finset.card_image_of_injective _ old.injective]
    exact hQ.1
  have hNoFresh : fresh ∉ Q.image old := by
    intro hv
    obtain ⟨v,_,h⟩ := Finset.mem_image.mp hv
    exact Fin.castSucc_ne_last v h
  have hCard : (insert fresh (Q.image old)).card = m+1 := by
    simp [hNoFresh, hOldCard]
  have hW : z (Q.image old) = W Q := by
    have hbase := p3SidePotential_image_old_base
      m t old fresh (by intro v; exact Fin.castSucc_ne_last v)
      eligible W L Q
    change p3SidePotential m t old fresh eligible W L
      (Q.image old) = W Q
    rw [hbase]
    simp [p3BasePotential, hQ]
  have hContract : ∀ U : Finset (Fin a),
      (contractAt fresh z) (U.image old) = link U := by
    intro U
    have hnot : fresh ∉ U.image old := by
      intro hv
      obtain ⟨v, _, heq⟩ := Finset.mem_image.mp hv
      exact Fin.castSucc_ne_last v heq
    change (if fresh ∈ U.image old then 0 else
      z (insert fresh (U.image old))) = link U
    rw [if_neg hnot]
    exact p3CanonicalSidePotential_fresh_old_image
      m t eligible W L U
  have hCoboundary :
      coboundary (contractAt fresh z) (Q.image old) =
      coboundary link Q :=
    p3Coboundary_image_injective old link
      (contractAt fresh z) hContract Q
  have hSource :=
    p3SideHyper_canonicalZMod
      m t (a+1) old fresh eligible W L
      (insert fresh (Q.image old)) hCard
  change p1BitToZMod
    ((p3CanonicalSide m t eligible W L).canonicalSignTable
      (insert fresh (Q.image old))) =
    W Q + coboundary link Q
  calc
    p1BitToZMod
        ((p3CanonicalSide m t eligible W L).canonicalSignTable
          (insert fresh (Q.image old))) =
      coboundary z (insert fresh (Q.image old)) := hSource
    _ = z (Q.image old) +
        coboundary (contractAt fresh z) (Q.image old) :=
          coboundary_insert_eq_add_contractAt fresh z
            (Q.image old) hNoFresh
    _ = W Q + coboundary link Q := by rw [hW, hCoboundary]

end Hypertournaments
