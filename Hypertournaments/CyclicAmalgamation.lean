import Hypertournaments.CircularCut
import Hypertournaments.CyclicLocalType
import Hypertournaments.OnePointNonmixedAdmissible
import Hypertournaments.OrderedStrongSpan
import Mathlib.Data.Fintype.EquivFin

/-!
# Strong amalgamation of finite cyclic orders

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
the small-arity AP-to-SAP assertion. Compatible cuts turn the original span
into a span of finite linear orders. Their shuffle is closed into a circle
on the original exact-overlap carrier. Empty bases and empty sides are included.
-/

universe u v w

namespace Hypertournaments

/-- An increasing injection of linear presentations preserves their induced
ternary hypertournament orientations. -/
theorem preserves_circularCompatible_of_strictMono
    {V : Type u} {W : Type v} [LinearOrder V] [LinearOrder W]
    {A : Hyper 3 V} {B : Hyper 3 W}
    (hA : A.CircularCompatible (LinearOrder.toCircularOrder V))
    (hB : B.CircularCompatible (LinearOrder.toCircularOrder W))
    (e : V ↪ W) (he : StrictMono e) : Preserves A B e := by
  apply (preserves_iff_sbtw (LinearOrder.toCircularOrder V)
    (LinearOrder.toCircularOrder W) hA hB e).mpr
  intro a b c _ _ _
  change (a < b ∧ b < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b) ↔
    (e a < e b ∧ e b < e c ∨ e b < e c ∧ e c < e a ∨ e c < e a ∧ e a < e b)
  simp only [he.lt_iff_lt]

/-- A cut at any vertex is a linear presentation of the same intrinsic circle. -/
theorem Hyper.CircularCompatible.cut {V : Type u} {A : Hyper 3 V}
    {order : CircularOrder V} (hA : A.CircularCompatible order) (p : V) :
    A.CircularCompatible
      (@LinearOrder.toCircularOrder V (@CircularOrder.cutLinearOrder V order p)) := by
  intro t
  exact (hA t).trans (@CircularOrder.cut_sbtw_iff V order p (t 0) (t 1) (t 2))

/-- Every finite cyclic order, including the empty one, has a linear presentation. -/
theorem Hyper.IsCyclicOrder.exists_linear_presentation {V : Type u} [Finite V]
    {A : Hyper 3 V} (hA : A.IsCyclicOrder) :
    ∃ order : LinearOrder V, A.CircularCompatible (@LinearOrder.toCircularOrder V order) := by
  classical
  by_cases hV : Nonempty V
  · obtain ⟨order, horder⟩ := hA
    exact ⟨@CircularOrder.cutLinearOrder V order (Classical.choice hV), horder.cut _⟩
  · let : Fintype V := Fintype.ofFinite V
    let order : LinearOrder V := LinearOrder.lift' (Fintype.equivFin V)
      (Fintype.equivFin V).injective
    refine ⟨order, ?_⟩
    intro t
    exact (hV ⟨t 0⟩).elim

/-- The finite cyclic-order span has a common system of linear presentations.
For a nonempty base all three cuts use one common root; for an empty base the
side cuts can be chosen independently. -/
theorem cyclic_span_linear_presentations
    {A : Type u} {B : Type v} {C : Type w} [Finite B] [Finite C]
    (AA : Hyper 3 A) (BB : Hyper 3 B) (CC : Hyper 3 C)
    (f : A ↪ B) (g : A ↪ C)
    (hAB : Preserves AA BB f) (hAC : Preserves AA CC g)
    (hA : AA.IsCyclicOrder) (hB : BB.IsCyclicOrder) (hC : CC.IsCyclicOrder) :
    ∃ (orderA : LinearOrder A) (orderB : LinearOrder B) (orderC : LinearOrder C),
      BB.CircularCompatible (@LinearOrder.toCircularOrder B orderB) ∧
      CC.CircularCompatible (@LinearOrder.toCircularOrder C orderC) ∧
      @StrictMono A B orderA.toPreorder orderB.toPreorder f ∧
      @StrictMono A C orderA.toPreorder orderC.toPreorder g := by
  classical
  let : Finite A := Finite.of_injective f f.injective
  by_cases hne : Nonempty A
  · let p : A := Classical.choice hne
    obtain ⟨circleA, hcircleA⟩ := hA
    obtain ⟨circleB, hcircleB⟩ := hB
    obtain ⟨circleC, hcircleC⟩ := hC
    let : CircularOrder A := circleA
    let : CircularOrder B := circleB
    let : CircularOrder C := circleC
    refine ⟨CircularOrder.cutLinearOrder p, CircularOrder.cutLinearOrder (f p),
      CircularOrder.cutLinearOrder (g p), hcircleB.cut _, hcircleC.cut _, ?_, ?_⟩
    · exact CircularOrder.cutLinearOrder_strictMono f p (f p) rfl
        ((preserves_iff_sbtw circleA circleB hcircleA hcircleB f).mp hAB)
    · exact CircularOrder.cutLinearOrder_strictMono g p (g p) rfl
        ((preserves_iff_sbtw circleA circleC hcircleA hcircleC g).mp hAC)
  · obtain ⟨orderA, _⟩ := hA.exists_linear_presentation
    obtain ⟨orderB, hB'⟩ := hB.exists_linear_presentation
    obtain ⟨orderC, hC'⟩ := hC.exists_linear_presentation
    refine ⟨orderA, orderB, orderC, hB', hC', ?_, ?_⟩ <;>
      intro x y _ <;> exact (hne ⟨x⟩).elim

/-- Finite cyclic orders strongly amalgamate on the exact-overlap carrier,
retaining the original arbitrary orientation-preserving injections. -/
theorem cyclic_order_strong_span
    {A : Type u} {B : Type v} {C : Type w} [Finite B] [Finite C]
    (AA : Hyper 3 A) (BB : Hyper 3 B) (CC : Hyper 3 C)
    (f : A ↪ B) (g : A ↪ C)
    (hAB : Preserves AA BB f) (hAC : Preserves AA CC g)
    (hA : AA.IsCyclicOrder) (hB : BB.IsCyclicOrder) (hC : CC.IsCyclicOrder) :
    ∃ D : Hyper 3 (FiniteStrongSpan.Carrier f g),
      D.IsCyclicOrder ∧ Preserves BB D (FiniteStrongSpan.left f g) ∧
        Preserves CC D (FiniteStrongSpan.right f g) := by
  classical
  let : Finite A := Finite.of_injective f f.injective
  let : Fintype A := Fintype.ofFinite A
  let : Fintype B := Fintype.ofFinite B
  let : Fintype C := Fintype.ofFinite C
  obtain ⟨orderA, orderB, orderC, hB', hC', hf, hg⟩ :=
    cyclic_span_linear_presentations AA BB CC f g hAB hAC hA hB hC
  let : LinearOrder A := orderA
  let : LinearOrder B := orderB
  let : LinearOrder C := orderC
  obtain ⟨order, hi, hj⟩ := OrderedStrongSpan.shuffle_orders f g hf hg
    (FiniteStrongSpan.left f g) (FiniteStrongSpan.right f g)
    (FiniteStrongSpan.left f g).injective (FiniteStrongSpan.right f g).injective
    (by
      intro x y hxy
      obtain ⟨a, ha, hb⟩ := (FiniteStrongSpan.overlap f g x y).mp hxy
      exact ⟨a, ha.symm, hb.symm⟩)
  let : LinearOrder (FiniteStrongSpan.Carrier f g) := order
  let : CircularOrder (FiniteStrongSpan.Carrier f g) := LinearOrder.toCircularOrder _
  let D : Hyper 3 (FiniteStrongSpan.Carrier f g) := Hyper.ofCircularOrder
  have hD : D.CircularCompatible (LinearOrder.toCircularOrder _) :=
    Hyper.ofCircularOrder_circularCompatible _
  refine ⟨D, Hyper.ofCircularOrder_isCyclicOrder, ?_, ?_⟩
  · exact preserves_circularCompatible_of_strictMono hB' hD (FiniteStrongSpan.left f g) hi
  · exact preserves_circularCompatible_of_strictMono hC' hD (FiniteStrongSpan.right f g) hj

/-- The cyclic local palette has finite strong amalgamation against the original
orientation-preserving embeddings, with exactly the prescribed overlap. -/
theorem cyclic_strong_span
    {A : Type u} {B : Type v} {C : Type w} [Finite B] [Finite C]
    (AA : Hyper 3 A) (BB : Hyper 3 B) (CC : Hyper 3 C)
    (f : A ↪ B) (g : A ↪ C)
    (hAB : Preserves AA BB f) (hAC : Preserves AA CC g)
    (hB : Admissible {2} BB) (hC : Admissible {2} CC) :
    ∃ D : Hyper 3 (FiniteStrongSpan.Carrier f g),
      Admissible {2} D ∧ Preserves BB D (FiniteStrongSpan.left f g) ∧
        Preserves CC D (FiniteStrongSpan.right f g) := by
  have hA : Admissible {2} AA := by
    intro t
    rw [localIndex_preserves AA BB f hAB t]
    exact hB (t.trans f)
  obtain ⟨D, hD, hi, hj⟩ := cyclic_order_strong_span AA BB CC f g hAB hAC
    ((Hyper.admissible_two_iff_isCyclicOrder AA).mp hA)
    ((Hyper.admissible_two_iff_isCyclicOrder BB).mp hB)
    ((Hyper.admissible_two_iff_isCyclicOrder CC).mp hC)
  exact ⟨D, (Hyper.admissible_two_iff_isCyclicOrder D).mpr hD, hi, hj⟩

end Hypertournaments
