import Hypertournaments.OddToggleP1PadCorePartition
import Hypertournaments.OddToggleP1CanonicalLinks

/-!
# Canonical link-row counting splits into pad and six-core columns

For the normalized p1 one-point diagram the row at an arbitrary old
vertex v contains 4k pad columns and six core columns. Their images
are disjoint and together comprise the whole old vertex set.

This is an *exact natural-number* count identity for the actual
canonical link table. It supplies the accounting bridge needed to
combine previously certified pad-column and six-core row parities.
It does not require side admissibility or ordinary AP.
-/

namespace Hypertournaments

/-- Number of positive canonical links in the row indexed by v. -/
def p1CanonicalRowPositiveCount (k : ℕ) (left : Bool)
    (v : Fin (4*k+6)) : ℕ :=
  (Finset.univ.filter (fun w : Fin (4*k+6) =>
    p1CanonicalLink k left v w = true)).card

/-- The exact row count is the sum of the contributions from
the 4k old pad coordinates and the last six core coordinates. -/
theorem p1CanonicalRowPositiveCount_split
    (k : ℕ) (left : Bool) (v : Fin (4*k+6)) :
    p1CanonicalRowPositiveCount k left v =
      (Finset.univ.filter (fun s : Fin (2*(2*k)) =>
        p1CanonicalLink k left v (p1PadAt k s) = true)).card +
      (Finset.univ.filter (fun j : Fin 6 =>
        p1CanonicalLink k left v (p1CoreAt k j) = true)).card := by
  classical
  let pads : Finset (Fin (4*k+6)) :=
    (Finset.univ : Finset (Fin (2*(2*k)))).image (p1PadAt k)
  let core : Finset (Fin (4*k+6)) :=
    (Finset.univ : Finset (Fin 6)).image (p1CoreAt k)
  let P : Fin (4*k+6) → Prop :=
    fun w => p1CanonicalLink k left v w = true
  have hcover : pads ∪ core = Finset.univ :=
    p1PadCore_images_cover k
  have hdisj : Disjoint pads core :=
    p1PadCore_images_disjoint k
  have hfilter :
      (Finset.univ : Finset (Fin (4*k+6))).filter P =
        (pads.filter P) ∪ (core.filter P) := by
    rw [← hcover, Finset.filter_union]
  have hfilterdisj : Disjoint (pads.filter P) (core.filter P) :=
    hdisj.mono (Finset.filter_subset P pads)
      (Finset.filter_subset P core)
  have hpad :
      (pads.filter P).card =
        (Finset.univ.filter (fun s : Fin (2*(2*k)) =>
          P (p1PadAt k s))).card := by
    dsimp [pads]
    rw [Finset.filter_image]
    exact Finset.card_image_of_injective _
      (p1PadAt_injective k)
  have hcore :
      (core.filter P).card =
        (Finset.univ.filter (fun j : Fin 6 =>
          P (p1CoreAt k j))).card := by
    dsimp [core]
    rw [Finset.filter_image]
    exact Finset.card_image_of_injective _
      (p1CoreAt_injective k)
  unfold p1CanonicalRowPositiveCount
  rw [hfilter, Finset.card_union_of_disjoint hfilterdisj,
      hpad, hcore]
  rfl

end Hypertournaments
