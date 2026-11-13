import Hypertournaments.PotentialAmalgamation
import Hypertournaments.EvenPotentialGauge
import Hypertournaments.EvenSwitching
import Hypertournaments.Amalgamation

/-!
# Strong amalgamation of finite even hypertournaments

Choose potentials on the two sides and align their restrictions by a
relative gauge change. The resulting compatible potentials strongly
amalgamate; their coboundary is an even strong amalgam of the original
structures. This also proves ordinary amalgamation against the existing
local-index switching palette.
-/

namespace Hypertournaments

universe u v w

/-- Finite even hypertournaments of odd arity at least three strongly
amalgamate on the explicit carrier with exactly the prescribed overlap. -/
theorem even_strong_span {r : ℕ} (hr : Even r) (hr2 : 2 ≤ r)
    {A : Type u} {B : Type v} {C : Type w} [Finite B] [Finite C]
    (AA : Hyper (r + 1) A) (BB : Hyper (r + 1) B) (CC : Hyper (r + 1) C)
    (f : A ↪ B) (g : A ↪ C)
    (hAB : Preserves AA BB f) (hAC : Preserves AA CC g)
    (hB : BB.IsEven) (hC : CC.IsEven) :
    ∃ D : Hyper (r + 1) (FiniteStrongSpan.Carrier f g),
      D.IsEven ∧ Preserves BB D (FiniteStrongSpan.left f g) ∧
        Preserves CC D (FiniteStrongSpan.right f g) := by
  classical
  let : Finite A := Finite.of_injective f f.injective
  obtain ⟨φB, hφB⟩ := BB.exists_potential hr hB
  obtain ⟨φC, hφC⟩ := CC.exists_potential hr hC
  have hbase : IsPotential (CC.pullback g) (φB.pullback f) := by
    intro t
    calc
      tupleCoboundary (fun s => p1BitToZMod ((φB.pullback f).orient s)) t =
          p1BitToZMod (BB.orient (t.trans f)) := hφB (t.trans f)
      _ = p1BitToZMod (AA.orient t) := congrArg p1BitToZMod (hAB t)
      _ = p1BitToZMod ((CC.pullback g).orient t) :=
        congrArg p1BitToZMod (hAC t).symm
  obtain ⟨φC', hφC', hbaseC⟩ := hφC.exists_aligned (φB.pullback f) g hbase (by omega)
  obtain ⟨D, φD, hD, _, _, hi, hj⟩ := potential_strong_span hr hr2
    (φB.pullback f) φB φC' BB CC f g (fun _ => rfl) hbaseC hφB hφC'
  exact ⟨D, hD.isEven, hi, hj⟩

/-- Arbitrary compatible free vertex orders extend to the even strong
amalgam on the same exact-overlap carrier. -/
theorem even_ordered_strong_span {r : ℕ} (hr : Even r) (hr2 : 2 ≤ r)
    {A : Type u} {B : Type v} {C : Type w}
    [Finite A] [Finite B] [Finite C]
    [LinearOrder A] [LinearOrder B] [LinearOrder C]
    (AA : Hyper (r + 1) A) (BB : Hyper (r + 1) B) (CC : Hyper (r + 1) C)
    (f : A ↪o B) (g : A ↪o C)
    (hAB : Preserves AA BB f.toEmbedding) (hAC : Preserves AA CC g.toEmbedding)
    (hB : BB.IsEven) (hC : CC.IsEven) :
    ∃ (order : LinearOrder (FiniteStrongSpan.Carrier f.toEmbedding g.toEmbedding))
      (D : Hyper (r + 1) (FiniteStrongSpan.Carrier f.toEmbedding g.toEmbedding)),
      D.IsEven ∧ Preserves BB D (FiniteStrongSpan.left f.toEmbedding g.toEmbedding) ∧
      Preserves CC D (FiniteStrongSpan.right f.toEmbedding g.toEmbedding) ∧
      (∀ x y : B, x < y → @LT.lt _ order.toLT
        (FiniteStrongSpan.left f.toEmbedding g.toEmbedding x)
        (FiniteStrongSpan.left f.toEmbedding g.toEmbedding y)) ∧
      (∀ x y : C, x < y → @LT.lt _ order.toLT
        (FiniteStrongSpan.right f.toEmbedding g.toEmbedding x)
        (FiniteStrongSpan.right f.toEmbedding g.toEmbedding y)) := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let : Fintype B := Fintype.ofFinite B
  let : Fintype C := Fintype.ofFinite C
  obtain ⟨order, hiOrder, hjOrder⟩ := OrderedStrongSpan.exists_order_on_carrier f g
  obtain ⟨D, hD, hi, hj⟩ := even_strong_span hr hr2 AA BB CC
    f.toEmbedding g.toEmbedding hAB hAC hB hC
  exact ⟨order, D, hD, hi, hj, hiOrder, hjOrder⟩

/-- The shared switching palette has strong amalgamation for every odd
arity at least three, on arbitrary finite vertex types. -/
theorem switching_strong_span {n : ℕ} (hn : Odd n) (hn3 : 3 ≤ n)
    {A : Type u} {B : Type v} {C : Type w} [Finite B] [Finite C]
    (AA : Hyper n A) (BB : Hyper n B) (CC : Hyper n C)
    (f : A ↪ B) (g : A ↪ C) (hAB : Preserves AA BB f) (hAC : Preserves AA CC g)
    (hB : Admissible (switchingAllowed n) BB) (hC : Admissible (switchingAllowed n) CC) :
    ∃ D : Hyper n (FiniteStrongSpan.Carrier f g),
      Admissible (switchingAllowed n) D ∧
        Preserves BB D (FiniteStrongSpan.left f g) ∧
        Preserves CC D (FiniteStrongSpan.right f g) := by
  obtain ⟨k, hk⟩ := hn
  have hnEq : n = 2 * k + 1 := by omega
  subst n
  have hr : Even (2 * k) := ⟨k, by omega⟩
  have hodd : Odd (2 * k + 1) := ⟨k, by omega⟩
  obtain ⟨D, hD, hi, hj⟩ := even_strong_span hr (by omega) AA BB CC f g hAB hAC
    ((BB.admissible_switching_iff_isEven hodd).mp hB)
    ((CC.admissible_switching_iff_isEven hodd).mp hC)
  exact ⟨D, (D.admissible_switching_iff_isEven hodd).mpr hD, hi, hj⟩

/-- Positive amalgamation for the switching alternative, stated against
the original ordinary-AP interface used by the negative classification. -/
theorem switching_hasAP (n : ℕ) (hn : Odd n) (hn3 : 3 ≤ n) :
    HasAP n (switchingAllowed n) := by
  classical
  intro a b c A B C _hA hB hC f g hf hg
  obtain ⟨D, hD, hi, hj⟩ := switching_strong_span hn hn3 A B C f g hf hg hB hC
  let e := Fintype.equivFin (FiniteStrongSpan.Carrier f g)
  let D' := D.pullback e.symm.toEmbedding
  let i := (FiniteStrongSpan.left f g).trans e.toEmbedding
  let j := (FiniteStrongSpan.right f g).trans e.toEmbedding
  refine ⟨Fintype.card (FiniteStrongSpan.Carrier f g), D', i, j,
    admissible_pullback D e.symm.toEmbedding hD, ?_, ?_, ?_⟩
  · intro t
    have ht : (t.trans i).trans e.symm.toEmbedding = t.trans (FiniteStrongSpan.left f g) := by
      ext k
      simp [i]
    change D.orient ((t.trans i).trans e.symm.toEmbedding) = _
    rw [ht]
    exact hi t
  · intro t
    have ht : (t.trans j).trans e.symm.toEmbedding = t.trans (FiniteStrongSpan.right f g) := by
      ext k
      simp [j]
    change D.orient ((t.trans j).trans e.symm.toEmbedding) = _
    rw [ht]
    exact hj t
  · intro x
    exact congrArg e (FiniteStrongSpan.commutes f g x)

end Hypertournaments
