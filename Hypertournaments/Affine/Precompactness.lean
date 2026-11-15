import Hypertournaments.Affine.ExpansionLanguage
import Mathlib.Order.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Basic.Finite.Sum

/-!
# Finitely many potential-and-order expansions of each finite reduct

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
"Further potential constructions". Finiteness is proved on the fixed
carrier itself, before passing to isomorphism classes.
-/

universe u v w

namespace Hypertournaments.Affine

/-- Finite raw and effective palettes give a finite relational expansion language. -/
theorem expansion_language_rel_finite {Q : Type u} {G : Type v} [AddCommGroup G]
    [Finite Q] [Finite G] (r : ℕ) (d : Data Q G) :
    Finite (orderedExpansionLanguage r d).RelSymbol := by
  change Finite ((G ⊕ Q) ⊕ Unit)
  infer_instance

/-- The expansion names only relations and introduces no function symbols. -/
theorem expansion_language_func_empty {Q : Type u} {G : Type v} [AddCommGroup G]
    (r : ℕ) (d : Data Q G) : IsEmpty (orderedExpansionLanguage r d).FuncSymbol := by
  change IsEmpty PEmpty
  infer_instance

/-- A finite carrier has only finitely many linear orders. -/
theorem finite_linearOrders (V : Type w) [Finite V] : Finite (LinearOrder V) := by
  classical
  let code : LinearOrder V → V → V → Bool :=
    fun o x y => decide (@LE.le V o.toLE x y)
  apply Finite.of_injective code
  intro A B h
  apply LinearOrder.ext
  intro x y
  have hh := congrFun (congrFun h x) y
  dsimp only [code] at hh
  exact decide_eq_decide.mp hh

/-- The potential and the free order on one fixed raw reduct. -/
def FixedExpansion {Q : Type u} {G : Type v} [AddCommGroup G]
    (d : Data Q G) {r : ℕ} {V : Type w} (raw : Labelled (r + 1) d.palette V) :=
  {p : Labelled r (Palette.affine d.offset) V // IsPotential d raw p} × LinearOrder V

/-- Precompactness requires only finiteness of the effective group and the
carrier; the fixed raw palette need not be finite for this statement. -/
theorem finite_fixed_expansions {Q : Type u} {G : Type v} [AddCommGroup G] [Finite G]
    (d : Data Q G) {r : ℕ} {V : Type w} [Finite V]
    (raw : Labelled (r + 1) d.palette V) : Finite (FixedExpansion d raw) := by
  let : Finite (LinearOrder V) := finite_linearOrders V
  unfold FixedExpansion
  infer_instance

/-- The actual native ordered structure named by a fixed expansion. -/
def fixedExpansionNative {Q : Type u} {G : Type v} [AddCommGroup G]
    {d : Data Q G} {r : ℕ} {V : Type w} {raw : Labelled (r + 1) d.palette V}
    (e : FixedExpansion d raw) :
    StructuralRamsey.Structure (orderedExpansionLanguage r d) V :=
  toOrderedExpansion ⟨raw, e.1.val, e.1.property⟩ e.2

/-- There are finitely many actual native expanded structures on each fixed
finite reduct, hence finitely many of their isomorphism types. -/
theorem ordered_expansions_finite {Q : Type u} {G : Type v} [AddCommGroup G] [Finite G]
    (d : Data Q G) {r : ℕ} {V : Type w} [Finite V]
    (raw : Labelled (r + 1) d.palette V) :
    Set.Finite (Set.range (fixedExpansionNative (d := d) (raw := raw))) := by
  let : Finite (FixedExpansion d raw) := finite_fixed_expansions d raw
  exact Set.finite_range _

end Hypertournaments.Affine
