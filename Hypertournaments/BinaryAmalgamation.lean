import Hypertournaments.BinaryOrder
import Hypertournaments.OnePointNonmixedAdmissible
import Hypertournaments.OrderedStrongSpan

/-!
# Strong amalgamation of transitive binary hypertournaments

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
the small-arity AP-to-SAP assertion. The local palette `{1}` is the
transitive-tournament class. Its intrinsic orientations reconstruct compatible
linear orders, which are shuffled on the original exact-overlap carrier.
The proof includes empty bases and empty side carriers.
-/

universe u v w

namespace Hypertournaments

/-- Transitive tournaments strongly amalgamate on the exact union of the
two given sides, retaining their original arbitrary preserving injections. -/
theorem binary_transitive_strong_span
    {A : Type u} {B : Type v} {C : Type w} [Finite B] [Finite C]
    (AA : Hyper 2 A) (BB : Hyper 2 B) (CC : Hyper 2 C)
    (f : A ↪ B) (g : A ↪ C)
    (hAB : Preserves AA BB f) (hAC : Preserves AA CC g)
    (hB : Admissible {1} BB) (hC : Admissible {1} CC) :
    ∃ D : Hyper 2 (FiniteStrongSpan.Carrier f g),
      Admissible {1} D ∧ Preserves BB D (FiniteStrongSpan.left f g) ∧
        Preserves CC D (FiniteStrongSpan.right f g) := by
  classical
  let : Finite A := Finite.of_injective f f.injective
  let : Fintype A := Fintype.ofFinite A
  let : Fintype B := Fintype.ofFinite B
  let : Fintype C := Fintype.ofFinite C
  have hA : Admissible {1} AA := by
    intro t
    rw [localIndex_preserves AA BB f hAB t]
    exact hB (t.trans f)
  let : LinearOrder A := AA.binaryLinearOrder hA
  let : LinearOrder B := BB.binaryLinearOrder hB
  let : LinearOrder C := CC.binaryLinearOrder hC
  have hf : StrictMono f :=
    (preserves_iff_binaryLinearOrder_strictMono AA BB hA hB f).mp hAB
  have hg : StrictMono g :=
    (preserves_iff_binaryLinearOrder_strictMono AA CC hA hC g).mp hAC
  obtain ⟨order, hi, hj⟩ := OrderedStrongSpan.shuffle_orders f g hf hg
    (FiniteStrongSpan.left f g) (FiniteStrongSpan.right f g)
    (FiniteStrongSpan.left f g).injective (FiniteStrongSpan.right f g).injective
    (by
      intro x y hxy
      obtain ⟨a, ha, hb⟩ := (FiniteStrongSpan.overlap f g x y).mp hxy
      exact ⟨a, ha.symm, hb.symm⟩)
  let D : Hyper 2 (FiniteStrongSpan.Carrier f g) :=
    @Hyper.fromOrderedSigns 2 _ order (fun _ => false)
  refine ⟨D, @binary_order_model_admissible _ order, ?_, ?_⟩
  · let i := @OrderEmbedding.ofStrictMono B (FiniteStrongSpan.Carrier f g)
      (BB.binaryLinearOrder hB) order.toPreorder (FiniteStrongSpan.left f g)
      (fun _ _ hxy => hi _ _ hxy)
    have hmodel := @fromOrderedSigns_preserves 2 B (FiniteStrongSpan.Carrier f g)
      (BB.binaryLinearOrder hB) order i (fun _ => false) (fun _ => false) (fun _ => rfl)
    intro t
    exact (hmodel t).trans (BB.binaryLinearOrder_model_orient hB t).symm
  · let j := @OrderEmbedding.ofStrictMono C (FiniteStrongSpan.Carrier f g)
      (CC.binaryLinearOrder hC) order.toPreorder (FiniteStrongSpan.right f g)
      (fun _ _ hxy => hj _ _ hxy)
    have hmodel := @fromOrderedSigns_preserves 2 C (FiniteStrongSpan.Carrier f g)
      (CC.binaryLinearOrder hC) order j (fun _ => false) (fun _ => false) (fun _ => rfl)
    intro t
    exact (hmodel t).trans (CC.binaryLinearOrder_model_orient hC t).symm

end Hypertournaments
