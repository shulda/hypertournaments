import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Hypertournaments.OnePointJoint

/-!
# Canonical padding geometry for ordinary one-point joints

Given a lower-arity one-point span on a old vertices and m auxiliary
padding vertices, we number its hypothetical higher-arity joint on
Fin (m+a+2). Pads are numbered 0,...,m-1, followed by all a old
vertices and then the two distinct new vertices.

These maps are injective *vertex* embeddings. They are unrelated to
the orientation-preservation property, which must be established by
each actual suspension construction. The range-disjointness is the
precise hypothesis needed by the two-pad intrinsic reconstruction.
-/

namespace Hypertournaments

/-- Include the m padding vertices at the start of the canonical
higher-arity ordinary one-point joint. -/
def canonicalPadToJoint (m a : ℕ) : Fin m ↪ Fin (m + a + 2) where
  toFun z := ⟨z.val, by omega⟩
  inj' := by
    intro x y h
    have hv := congrArg (fun z : Fin (m + a + 2) => z.val) h
    apply Fin.ext
    exact hv

/-- Include the a+2 vertices of the lower-arity ordinary joint as
the final a+2 vertices of the padded joint. -/
def canonicalOldToJoint (m a : ℕ) :
    Fin (a + 2) ↪ Fin (m + a + 2) where
  toFun x := ⟨m + x.val, by omega⟩
  inj' := by
    intro x y h
    apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp at hv
    omega

/-- The pad family and the entire lower-arity joint are disjoint. -/
theorem canonicalPadToJoint_not_mem_old
    (m a : ℕ) (z : Fin m) :
    canonicalPadToJoint m a z ∉
      Set.range (canonicalOldToJoint m a) := by
  rintro ⟨x, hx⟩
  have hv := congrArg (fun w : Fin (m + a + 2) => w.val) hx
  change m + x.val = z.val at hv
  have hz : z.val < m := z.isLt
  omega

/-- Include a lower-arity one-point extension among the final a+1
positions of a padded extension, with its new point still last. -/
def canonicalOldToSide (m a : ℕ) :
    Fin (a + 1) ↪ Fin (m + a + 1) where
  toFun x := ⟨m + x.val, by omega⟩
  inj' := by
    intro x y h
    apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp at hv
    omega

/-- The old left side injection commutes with the canonical inclusion
of a one-point extension into its ordinary joint. -/
theorem canonicalOld_left_commutes (m a : ℕ) :
    (canonicalOldToSide m a).trans (leftJointInclusion (m + a)) =
      (leftJointInclusion a).trans (canonicalOldToJoint m a) := by
  ext x
  rfl

/-- The old right side injection also commutes with the canonical
ordinary joint: right new vertices are mapped to the final position. -/
theorem canonicalOld_right_commutes (m a : ℕ) :
    (canonicalOldToSide m a).trans (rightJointInclusion (m + a)) =
      (rightJointInclusion a).trans (canonicalOldToJoint m a) := by
  ext x
  change
    (rightJointInclusion (m + a) (canonicalOldToSide m a x)).val =
      (canonicalOldToJoint m a (rightJointInclusion a x)).val
  rcases x.eq_castSucc_or_eq_last with ⟨y, rfl⟩ | rfl
  · let z : Fin (m + a) := ⟨m + y.val, by omega⟩
    have hz :
        canonicalOldToSide m a y.castSucc = z.castSucc := by
      apply Fin.ext
      rfl
    rw [hz, rightJointInclusion_old (m + a) z,
      rightJointInclusion_old a y]
    rfl
  · have hz :
        canonicalOldToSide m a (Fin.last a) =
          Fin.last (m + a) := by
      apply Fin.ext
      rfl
    rw [hz, rightJointInclusion_new (m + a), rightJointInclusion_new a]
    rfl

end Hypertournaments
