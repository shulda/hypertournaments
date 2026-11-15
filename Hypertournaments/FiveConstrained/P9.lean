import Hypertournaments.FiveConstrained.Mask
import Hypertournaments.PairCancellation
import Hypertournaments.PartialHyper
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-!
# The five-vertex pair-cancelling hypertournament

The July classification source defines `P9` by the positive increasing
triples `012, 023, 034`, namely mask `41` in the lexicographic convention.
Here each bit is literally the Boolean value of `Hyper.orient` on the
corresponding increasing triple. The November technical note reverses the
names of the two signs; the intrinsic structure below keeps one convention.
-/

namespace Hypertournaments.FiveConstrained

/-- The explicitly specified five-vertex forbidden structure `P9`. -/
def p9 : Hyper 3 (Fin 5) := maskHyper 5 41

private def distinctTriple (u v w : Fin 5)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) : Fin 3 ↪ Fin 5 where
  toFun := ![u, v, w]
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

private theorem p9_nonconstant_pair_links :
    ∀ u v : Fin 5, u ≠ v → ∃ w z : Fin 5,
      u ≠ w ∧ v ≠ w ∧ u ≠ z ∧ v ≠ z ∧
      orientAt 5 41 u.val v.val w.val ≠ orientAt 5 41 u.val v.val z.val := by
  decide

private theorem distinctTriple_pairLink (order : LinearOrder (Fin 5))
    (u v w : Fin 5) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    @IsPairLink 3 (Fin 5) order u v (distinctTriple u v w huv huw hvw) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have : i = 0 := Fin.ext hi
    subst i
    rfl
  · intro i hi
    have : i = 1 := Fin.ext hi
    subst i
    rfl
  · intro i j hi hij
    have hiBound := i.isLt
    have hjBound := j.isLt
    have hijVal : i.val < j.val := hij
    omega

/-- Every pair has genuinely nonconstant ternary link, independently of
the auxiliary order, so the existing completion theorem applies. -/
theorem p9_pairCancelling : PairCancelling p9 := by
  refine ⟨by decide, by simp, ?_⟩
  intro order u v huv
  obtain ⟨w, z, huw, hvw, huz, hvz, hdiff⟩ :=
    p9_nonconstant_pair_links u v huv
  refine ⟨distinctTriple u v w huv huw hvw,
    distinctTriple u v z huv huz hvz,
    distinctTriple_pairLink order u v w huv huw hvw,
    distinctTriple_pairLink order u v z huv huz hvz, ?_⟩
  exact hdiff

/-- The singleton forbidden family, represented only at cardinality five.
Omission still quantifies over every intrinsic orientation-preserving
injection, hence forbids every induced isomorphic copy. -/
def p9Family : ForbiddenFamily 3 := fun m =>
  {F | ∃ h : m = 5, h ▸ F = p9}

theorem p9_mem_family : p9 ∈ p9Family 5 := ⟨rfl, rfl⟩

theorem p9Family_pairCancelling (m : ℕ) (F : Hyper 3 (Fin m))
    (hF : F ∈ p9Family m) : PairCancelling F := by
  obtain ⟨h, hF⟩ := hF
  subst m
  have heq : F = p9 := by simpa using hF
  rw [heq]
  exact p9_pairCancelling

/-- The singleton-family notation is exactly omission of the original
five-vertex structure along arbitrary injections, on every carrier. -/
theorem omits_p9Family_iff {V : Type*} (A : Hyper 3 V) :
    Omits p9Family A ↔ ∀ e : Fin 5 ↪ V, ¬ Preserves p9 A e := by
  constructor
  · intro h e
    exact h 5 p9 p9_mem_family e
  · intro h m F hF e
    obtain ⟨hm, hF⟩ := hF
    subst m
    have heq : F = p9 := by simpa using hF
    rw [heq]
    exact h e

end Hypertournaments.FiveConstrained
