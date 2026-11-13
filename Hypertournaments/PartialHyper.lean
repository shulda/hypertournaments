import Hypertournaments.FinitePresentation

/-!
# Partially prescribed alternating orientations

`none` is an unspecified n-set, not an additional orientation. Consistent
arbitrary relational inputs will be converted to this interface separately.
-/

universe u

namespace Hypertournaments

structure PartialHyper (n : ℕ) (V : Type u) where
  orient : (Fin n ↪ V) → Option Bool
  swap_flip : ∀ (f : Fin n ↪ V) (i j : Fin n), i ≠ j →
    orient ((Equiv.swap i j).toEmbedding.trans f) = (orient f).map Bool.not

/-- A completion keeps every orientation that was actually prescribed. -/
def PartialHyper.Extends {n : ℕ} {V : Type*}
    (P : PartialHyper n V) (D : Hyper n V) : Prop :=
  ∀ f b, P.orient f = some b → D.orient f = b

/-- A family of finite forbidden structures, represented on every finite cardinality. -/
abbrev ForbiddenFamily (n : ℕ) := ∀ m : ℕ, Set (Hyper n (Fin m))

/-- Omission uses arbitrary orientation-preserving injections. -/
def Omits {n : ℕ} {V : Type*} (family : ForbiddenFamily n) (A : Hyper n V) : Prop :=
  ∀ m (F : Hyper n (Fin m)), F ∈ family m → ∀ e : Fin m ↪ V, ¬ Preserves F A e

/-- A partial structure contains no fully prescribed forbidden copy. -/
def PartialHyper.Omits {n : ℕ} {V : Type*}
    (P : PartialHyper n V) (family : ForbiddenFamily n) : Prop :=
  ∀ m (F : Hyper n (Fin m)), F ∈ family m → ∀ e : Fin m ↪ V,
    ¬ (∀ t : Fin n ↪ Fin m, P.orient (t.trans e) = some (F.orient t))

/-- The missing pair domain is separate from the orientation table.
On an n-set exactly one orientation is prescribed iff it contains no missing pair. -/
def PartialHyper.HasCliqueDomain {n : ℕ} {V : Type*}
    (P : PartialHyper n V) (missing : Finset (V × V)) : Prop :=
  ∀ f : Fin n ↪ V, P.orient f ≠ none ↔
    ∀ p ∈ missing, ¬ (p.1 ∈ Set.range f ∧ p.2 ∈ Set.range f)

theorem tupleVertices_mem_range {n : ℕ} {V : Type*} [DecidableEq V]
    (f : Fin n ↪ V) (x : V) : x ∈ tupleVertices f ↔ x ∈ Set.range f := by
  simp only [tupleVertices, Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range]

/-- Restriction of a complete forbidden-free structure remains forbidden-free. -/
theorem omits_pullback {n : ℕ} {V W : Type*}
    {family : ForbiddenFamily n} {A : Hyper n W}
    (h : Omits family A) (e : V ↪ W) : Omits family (A.pullback e) := by
  intro m F hF f hp
  exact h m F hF (f.trans e) hp

/-- For finite spans, strong amalgamation has exactly the original ordinary
embedding interface plus the exact-overlap condition. -/
def HasStrongAmalgamation {n : ℕ} (family : ForbiddenFamily n) : Prop :=
  ∀ (a b c : ℕ) (A : Hyper n (Fin a)) (B : Hyper n (Fin b)) (C : Hyper n (Fin c)),
    Omits family A → Omits family B → Omits family C →
    ∀ (f : Fin a ↪ Fin b) (g : Fin a ↪ Fin c), Preserves A B f → Preserves A C g →
    ∃ (d : ℕ) (D : Hyper n (Fin d)) (i : Fin b ↪ Fin d) (j : Fin c ↪ Fin d),
      Omits family D ∧ Preserves B D i ∧ Preserves C D j ∧
      (∀ x, i (f x) = j (g x)) ∧
      (∀ y z, i y = j z → ∃ x, f x = y ∧ g x = z)

end Hypertournaments
