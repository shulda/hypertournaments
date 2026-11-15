import Hypertournaments.BinaryOrderHost
import Hypertournaments.BinaryPairHomogeneity

/-!
# Ordering property for unrestricted tournaments and hypertournaments

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`, binary
potential base case. Two Ramsey stages homogenize the two ordered edge
types independently; the directed triangle makes their colours agree.
-/

namespace Hypertournaments.Ramsey

open StructuralRamsey
open StructuralRamsey.Structure

/-- Tournaments have the full ordering property, with their two ordered edge
types handled separately rather than identified. -/
theorem binary_ordering_property
    {V : Type} [Finite V] (A : Hyper 2 V) :
    ∃ (W : Type) (_ : Finite W) (B : Hyper 2 W),
      ∀ (orderA : LinearOrder V) (orderB : LinearOrder W),
        Nonempty (Embedding (toOrderedNative A orderA) (toOrderedNative B orderB)) := by
  classical
  obtain ⟨U, hU, D, oldD, hAll, ⟨cycle⟩⟩ :=
    unrestricted_exists_all_order_host_with (by decide : 2 ≤ 2) A binaryCycle inferInstance
  let : Finite U := hU
  obtain ⟨X, hX, C₁, oldC₁, _, arrow₁⟩ :=
    exists_unrestricted_ordered_ramsey_witness (by decide : 2 ≤ 2)
      (binaryPair false) D inferInstance oldD Bool
  let : Finite X := hX
  obtain ⟨W, hW, B, oldB, _, arrow₂⟩ :=
    exists_unrestricted_ordered_ramsey_witness (by decide : 2 ≤ 2)
      (binaryPair true) C₁ inferInstance oldC₁ Bool
  refine ⟨W, hW, B, ?_⟩
  intro orderA orderB
  obtain ⟨g, hg⟩ := arrow₂ (@binaryPairColor true W _ orderB)
  obtain ⟨f, hf⟩ := arrow₁
    (fun e => binaryPairColor orderB (g.comp e))
  have hhom : ∀ (b : Bool)
      (e₁ e₂ : Embedding (orderedBinaryPair b) (toOrderedNative D oldD)),
      binaryPairColor orderB ((g.comp f).comp e₁) =
        binaryPairColor orderB ((g.comp f).comp e₂) := by
    intro b e₁ e₂
    cases b
    · exact hf e₁ e₂
    · exact hg (f.comp e₁) (f.comp e₂)
  rcases binary_pair_order_homogeneity D oldD B oldB orderB cycle (g.comp f) hhom with
    hmono | hanti
  · obtain ⟨e⟩ := hAll orderA
    have he : @StrictMono V U orderA.toPreorder oldD.toPreorder e := e.strictMono
    exact ⟨reorderEmbedding A B orderA orderA oldB orderB ((g.comp f).comp e)
      (hmono.comp he)⟩
  · let reversed : LinearOrder V := @OrderDual.instLinearOrder V orderA
    obtain ⟨e⟩ := hAll reversed
    have he : @StrictMono V U reversed.toPreorder oldD.toPreorder e := e.strictMono
    have hcomp : @StrictMono V W orderA.toPreorder orderB.toPreorder ((g.comp f).comp e) := by
      intro x y hxy
      exact hanti (he hxy)
    exact ⟨reorderEmbedding A B reversed orderA oldB orderB ((g.comp f).comp e) hcomp⟩

/-- Every unrestricted arity at least two has the ordering property. This
includes the binary potential class needed for even ternary structures. -/
theorem unrestricted_ordering_property {n : ℕ} (hn : 2 ≤ n)
    {V : Type} [Finite V] (A : Hyper n V) :
    ∃ (W : Type) (_ : Finite W) (B : Hyper n W),
      ∀ (orderA : LinearOrder V) (orderB : LinearOrder W),
        Nonempty (Embedding (toOrderedNative A orderA) (toOrderedNative B orderB)) := by
  by_cases htwo : n = 2
  · subst n
    exact binary_ordering_property A
  · have hthree : 3 ≤ n := by omega
    obtain ⟨W, hW, B, _, hAll⟩ := pair_cancelling_ordering_property hthree
      (emptyForbiddenFamily n) (emptyForbiddenFamily_pairCancelling n) A
      (omits_emptyForbiddenFamily A)
    exact ⟨W, hW, B, hAll⟩

end Hypertournaments.Ramsey
