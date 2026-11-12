import Hypertournaments.OddToggleP3ExplicitPotentials
import Hypertournaments.CoboundaryGauge

/-!
# The two explicit p3 one-point sides have a genuine common old base

The p3 random side potential uses the same old W coefficient table
on the image of the base, independently of its eligible missing
blocks and independent L/R coefficient families.

The unsigned cochain coboundary is natural under injective images:
if two cochains agree on the embedded old finite subsets then their
coboundaries agree on each embedded old (n+1)-vertex set.

Consequently every genuine intrinsic one-point side Hyper(m+1)
preserves the canonical potential-induced old Hyper(m+1), provided
the fresh vertex is disjoint from the image of the increasing old
embedding. This is an ACTUAL common-base statement, not a synthetic
Boolean diagram.

No age membership, failed-amalgamation or probabilistic conclusion
is asserted here.
-/

namespace Hypertournaments

/-- Erasing a vertex before or after applying an injective map
gives exactly the same finite set. -/
theorem p3Finset_image_erase
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (e : A ↪ B) (Q : Finset A) (v : A) :
    (Q.erase v).image e = (Q.image e).erase (e v) := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
    obtain ⟨hxne, hxmem⟩ := Finset.mem_erase.mp hx
    apply Finset.mem_erase.mpr
    constructor
    · intro hyEq
      exact hxne (e.injective (hxy.trans hyEq))
    · exact Finset.mem_image.mpr ⟨x, hxmem, hxy⟩
  · intro hy
    obtain ⟨hyne, hyimage⟩ := Finset.mem_erase.mp hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hyimage
    apply Finset.mem_image.mpr
    refine ⟨x, ?_, hxy⟩
    apply Finset.mem_erase.mpr
    constructor
    · intro hxEq
      apply hyne
      simpa [hxEq] using hxy.symm
    · exact hx

/-- Exact naturality of the unsigned F₂ cochain coboundary under
an injective vertex map, assuming source cochains agree on the
images of ALL old finite subsets. -/
theorem p3Coboundary_image_injective
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (e : A ↪ B)
    (zOld : Finset A → ZMod 2)
    (zSide : Finset B → ZMod 2)
    (h : ∀ U : Finset A, zSide (U.image e) = zOld U)
    (Q : Finset A) :
    coboundary zSide (Q.image e) = coboundary zOld Q := by
  classical
  have heinj : Set.InjOn (e : A → B) (↑Q) := by
    intro x _ y _ heq
    exact e.injective heq
  unfold coboundary
  calc
    (∑ v ∈ Q.image e, zSide ((Q.image e).erase v)) =
        ∑ v ∈ Q, zSide ((Q.image e).erase (e v)) := by
          simpa using
            (Finset.sum_image
              (s := Q) (g := (e : A → B))
              (f := fun w : B => zSide ((Q.image e).erase w))
              heinj)
    _ = ∑ v ∈ Q, zOld (Q.erase v) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [← p3Finset_image_erase e Q v]
      exact h (Q.erase v)

/-- Evaluating the genuine side potential on any image of an
old finite subset gives exactly the restricted common W potential. -/
theorem p3SidePotential_image_old_base
    (m t : ℕ) {V : Type*} [DecidableEq V]
    (old : Fin (m*t) ↪ V) (fresh : V)
    (hfresh : ∀ v : Fin (m*t), old v ≠ fresh)
    (eligible : Finset (Fin m))
    (W L : Finset (Fin (m*t)) → ZMod 2)
    (U : Finset (Fin (m*t))) :
    p3SidePotential m t old fresh eligible W L (U.image old) =
      p3BasePotential m t W U := by
  have hnot : fresh ∉ U.image old := by
    intro hmem
    obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hmem
    exact (hfresh v) heq
  rw [p3SidePotential_oldOnly m t old fresh eligible W L (U.image old) hnot]
  rw [p3SideOldPart_image m t old U]

/-- Every explicitly constructed p3 one-point side is a genuine
orientation-preserving extension of the canonical old base Hyper.
In particular the left and right sides (with common W) agree on all
old (m+1)-tuples, including permutations, as long as each has an
increasing old embedding with its fresh point disjoint. -/
theorem p3SideHyper_preserves_base
    (m t : ℕ) {V : Type*} [LinearOrder V]
    (old : Fin (m*t) ↪o V) (fresh : V)
    (hfresh : ∀ v : Fin (m*t), old v ≠ fresh)
    (eligible : Finset (Fin m))
    (W L : Finset (Fin (m*t)) → ZMod 2) :
    Preserves
      (p3HyperFromPotential (m+1) (m*t) (p3BasePotential m t W))
      (p3SideHyper m t old.toEmbedding fresh eligible W L)
      old.toEmbedding := by
  change Preserves
    (Hyper.fromOrderedSigns
      (fun Q => p3ZMod2ToBool
        (coboundary (p3BasePotential m t W) Q)))
    (Hyper.fromOrderedSigns
      (fun Q => p3ZMod2ToBool
        (coboundary
          (p3SidePotential m t old.toEmbedding fresh eligible W L) Q)))
    old.toEmbedding
  apply fromOrderedSigns_preserves old
    (fun Q => p3ZMod2ToBool (coboundary (p3BasePotential m t W) Q))
    (fun Q => p3ZMod2ToBool
      (coboundary
        (p3SidePotential m t old.toEmbedding fresh eligible W L) Q))
  intro Q
  apply congrArg p3ZMod2ToBool
  apply p3Coboundary_image_injective old.toEmbedding
    (p3BasePotential m t W)
    (p3SidePotential m t old.toEmbedding fresh eligible W L)
  intro U
  exact p3SidePotential_image_old_base
    m t old.toEmbedding fresh hfresh eligible W L U

end Hypertournaments
