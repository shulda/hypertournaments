import Hypertournaments.CanonicalPadJoint
import Hypertournaments.TwoPadCommutingSquare

/-!
# Padding vertices inside each higher-arity one-point side

A padded source side has vertices Fin(m+a+1): first the m pads,
then the a old base vertices and one new source point. This module
provides the pad injection and proves that it is disjoint from the
canonical old-source injection. Each source pad maps to the same pad
in either canonical joint inclusion.

Together with CanonicalPadJoint, these are the exact geometric
commuting squares needed for ordinary higher-arity AP reflection.
-/

namespace Hypertournaments

/-- The m auxiliary pad vertices of a padded one-point extension. -/
def canonicalPadToSide (m a : ℕ) : Fin m ↪ Fin (m + a + 1) where
  toFun z := ⟨z.val, by omega⟩
  inj' := by
    intro x y h
    apply Fin.ext
    exact congrArg (fun w : Fin (m + a + 1) => w.val) h

/-- No side pad belongs to the image of an original old source vertex. -/
theorem canonicalPadToSide_not_mem_old
    (m a : ℕ) (z : Fin m) :
    canonicalPadToSide m a z ∉ Set.range (canonicalOldToSide m a) := by
  rintro ⟨x, hx⟩
  have hv := congrArg (fun w : Fin (m + a + 1) => w.val) hx
  change m + x.val = z.val at hv
  have hz := z.isLt
  omega

/-- Left one-point inclusion sends every pad of the left side to
the corresponding pad of the canonical higher-arity joint. -/
theorem canonicalPad_left_commutes (m a : ℕ) :
    (canonicalPadToSide m a).trans (leftJointInclusion (m + a)) =
    canonicalPadToJoint m a := by
  ext z
  rfl

/-- Right one-point inclusion also fixes all shared auxiliary pads. -/
theorem canonicalPad_right_commutes (m a : ℕ) :
    (canonicalPadToSide m a).trans (rightJointInclusion (m + a)) =
    canonicalPadToJoint m a := by
  ext z
  let y : Fin (m + a) := ⟨z.val, by omega⟩
  have hy : canonicalPadToSide m a z = y.castSucc := by
    apply Fin.ext
    rfl
  change (rightJointInclusion (m + a)
    (canonicalPadToSide m a z)).val = (canonicalPadToJoint m a z).val
  rw [hy, rightJointInclusion_old (m + a) y]
  rfl

end Hypertournaments
