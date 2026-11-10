import Hypertournaments.OddToggleP1CanonicalLinks

/-!
# Canonical partition of the 4k+6 old p1 vertices into pads and core

The exceptional n=4k+5 source diagrams consist of 4k auxiliary
vertices, followed by exactly six core vertices. The intrinsic
universe is Fin(4k+6), and all link-row parity calculations need an
exact finite decomposition into these two disjoint ordered blocks.

This module proves the two canonical injections are injective,
have disjoint images, and cover the full old universe. It is
independent of the parity table and the AP argument.
-/

namespace Hypertournaments

/-- The canonical pad vertex with old coordinate s. -/
def p1PadAt (k : ℕ) (s : Fin (2*(2*k))) : Fin (4*k+6) :=
  ⟨s.val, by have hs := s.isLt; omega⟩

theorem p1PadAt_lt (k : ℕ) (s : Fin (2*(2*k))) :
    (p1PadAt k s).val < 4*k := by
  dsimp [p1PadAt]
  have hs := s.isLt
  omega

theorem p1PadAt_injective (k : ℕ) :
    Function.Injective (p1PadAt k) := by
  intro s t h
  apply Fin.ext
  have hv := congrArg Fin.val h
  exact hv

theorem p1CoreAt_injective (k : ℕ) :
    Function.Injective (p1CoreAt k) := by
  intro s t h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 4*k + s.val = 4*k + t.val at hv
  omega

theorem p1CoreAt_ge (k : ℕ) (j : Fin 6) :
    4*k ≤ (p1CoreAt k j).val := by
  change 4*k ≤ 4*k+j.val
  omega

/-- Every old vertex is uniquely in either the pad or core
segment, witnessed by its original numeric coordinates. -/
theorem p1OldVertex_pad_or_core (k : ℕ) (v : Fin (4*k+6)) :
    (∃ s : Fin (2*(2*k)), p1PadAt k s = v) ∨
    (∃ j : Fin 6, p1CoreAt k j = v) := by
  by_cases hv : v.val < 4*k
  · left
    refine ⟨⟨v.val, by omega⟩, ?_⟩
    apply Fin.ext
    rfl
  · right
    have hj : v.val - 4*k < 6 := by
      have hmax := v.isLt
      omega
    refine ⟨⟨v.val - 4*k, hj⟩, ?_⟩
    apply Fin.ext
    change 4*k + (v.val - 4*k) = v.val
    omega

/-- The two canonical old-coordinate blocks cover the universe. -/
theorem p1PadCore_images_cover (k : ℕ) :
    ((Finset.univ : Finset (Fin (2*(2*k)))).image (p1PadAt k)) ∪
      ((Finset.univ : Finset (Fin 6)).image (p1CoreAt k)) =
        (Finset.univ : Finset (Fin (4*k+6))) := by
  ext v
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ,
    true_and, iff_true]
  exact p1OldVertex_pad_or_core k v

/-- The canonical pad and core images are disjoint. -/
theorem p1PadCore_images_disjoint (k : ℕ) :
    Disjoint
      ((Finset.univ : Finset (Fin (2*(2*k)))).image (p1PadAt k))
      ((Finset.univ : Finset (Fin 6)).image (p1CoreAt k)) := by
  apply Finset.disjoint_left.mpr
  intro v hv hc
  obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hv
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hc
  have hval := (congrArg Fin.val hs).trans
    (congrArg Fin.val hj).symm
  have hpad := p1PadAt_lt k s
  have hcore := p1CoreAt_ge k j
  omega

end Hypertournaments
