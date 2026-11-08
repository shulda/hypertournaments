import Hypertournaments.Basic

/-!
# Ordered sign presentations of intrinsic hypertournaments

Given a linear order on V, the permutation that sorts any injective
tuple changes parity under a transposition of its indices.
This is the key tool for importing the explicit positive-sign
catalogues in the mathematical technical note without naming the
auxiliary linear order in the final hypertournament language.
-/

namespace Hypertournaments

variable {n : ℕ} {V : Type*} [LinearOrder V]

/-- Sorting a tuple after swapping coordinates swaps the sorting
permutation on the left. The hypothesis that the tuple is injective
is essential for uniqueness of the sorting permutation. -/
theorem sort_swap_embedding (f : Fin n ↪ V) (i j : Fin n) :
    Tuple.sort (fun x => f (Equiv.swap i j x)) =
      Equiv.swap i j * Tuple.sort (f : Fin n → V) := by
  let σ : Equiv.Perm (Fin n) := Equiv.swap i j
  have hsorted :
      ((f : Fin n → V) ∘ σ) ∘ Tuple.sort ((f : Fin n → V) ∘ σ) =
        (f : Fin n → V) ∘ Tuple.sort (f : Fin n → V) :=
    Tuple.comp_perm_comp_sort_eq_comp_sort
  have hperm :
      σ * Tuple.sort ((f : Fin n → V) ∘ σ) =
        Tuple.sort (f : Fin n → V) := by
    apply Equiv.ext
    intro x
    apply f.injective
    simpa only [Function.comp_apply, Equiv.Perm.mul_apply]
      using congrFun hsorted x
  have hcancel := congrArg (fun p : Equiv.Perm (Fin n) => σ⁻¹ * p) hperm
  have hfun : (fun x => f (Equiv.swap i j x)) =
      ((f : Fin n → V) ∘ (Equiv.swap i j : Fin n → Fin n)) := rfl
  rw [hfun]
  simpa [σ, mul_assoc] using hcancel

/-- Swapping distinct coordinates negates the sign of the
sorting permutation. -/
theorem sort_swap_sign (f : Fin n ↪ V) (i j : Fin n) (hij : i ≠ j) :
    (Tuple.sort (fun x => f (Equiv.swap i j x))).sign =
      - (Tuple.sort (f : Fin n → V)).sign := by
  rw [sort_swap_embedding, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]
  simp

/-- The underlying finite set of vertices of an injective tuple. -/
def tupleVertices {n : ℕ} {V : Type*} [DecidableEq V]
    (f : Fin n ↪ V) : Finset V :=
  Finset.univ.image f

/-- Reordering a tuple does not change its underlying vertex set. -/
theorem tupleVertices_swap {n : ℕ} {V : Type*} [DecidableEq V]
    (f : Fin n ↪ V) (i j : Fin n) :
    tupleVertices ((Equiv.swap i j).toEmbedding.trans f) = tupleVertices f := by
  ext v
  simp only [tupleVertices, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨Equiv.swap i j x, hx⟩
  · rintro ⟨x, hx⟩
    refine ⟨Equiv.swap i j x, ?_⟩
    simpa using hx

/-- Turn a table of signs on unordered n-element vertex sets into
an alternating orientation on injective ordered tuples.
The canonical order is used only to present the sign table. -/
def orderedSignOrientation {n : ℕ} {V : Type*} [LinearOrder V]
    (signs : Finset V → Bool) (f : Fin n ↪ V) : Bool :=
  if (Tuple.sort (f : Fin n → V)).sign = 1 then
    signs (tupleVertices f)
  else
    !(signs (tupleVertices f))

/-- Any sign table relative to an auxiliary order defines an
intrinsic hypertournament, with the correct transposition law. -/
def Hyper.fromOrderedSigns {n : ℕ} {V : Type*} [LinearOrder V]
    (signs : Finset V → Bool) : Hyper n V where
  orient := orderedSignOrientation signs
  swap_flip := by
    intro f i j hij
    change orderedSignOrientation signs ((Equiv.swap i j).toEmbedding.trans f) =
      !(orderedSignOrientation signs f)
    change
      (if (Tuple.sort (fun x => f (Equiv.swap i j x))).sign = 1 then
        signs (tupleVertices ((Equiv.swap i j).toEmbedding.trans f))
       else
        !(signs (tupleVertices ((Equiv.swap i j).toEmbedding.trans f)))) =
      !(if (Tuple.sort (f : Fin n → V)).sign = 1 then
          signs (tupleVertices f)
        else
          !(signs (tupleVertices f)))
    rw [sort_swap_sign f i j hij, tupleVertices_swap]
    rcases Int.units_eq_one_or (Tuple.sort (f : Fin n → V)).sign with h | h
    · simp [h]
    · simp [h]

/-- Strictly increasing embeddings do not change the sorting
permutation of an injective tuple. -/
theorem sort_map_orderEmbedding {n : ℕ} {V W : Type*}
    [LinearOrder V] [LinearOrder W]
    (f : Fin n ↪ V) (g : V ↪o W) :
    Tuple.sort ((f.trans g.toEmbedding : Fin n ↪ W) : Fin n → W) =
      Tuple.sort (f : Fin n → V) := by
  let ff : Fin n → W := fun x => g (f x)
  change Tuple.sort ff = Tuple.sort (f : Fin n → V)
  have hm₁ : Monotone (ff ∘ Tuple.sort (f : Fin n → V)) :=
    g.monotone.comp (Tuple.monotone_sort (f : Fin n → V))
  have hm₂ : Monotone (ff ∘ Tuple.sort ff) :=
    Tuple.monotone_sort ff
  have heq : ff ∘ Tuple.sort (f : Fin n → V) =
      ff ∘ Tuple.sort ff :=
    Tuple.unique_monotone hm₁ hm₂
  apply Equiv.ext
  intro x
  apply f.injective
  apply g.injective
  exact (congrFun heq x).symm

/-- The vertex set of a tuple behaves naturally under embeddings. -/
theorem tupleVertices_map_orderEmbedding {n : ℕ} {V W : Type*}
    [LinearOrder V] [LinearOrder W]
    (f : Fin n ↪ V) (g : V ↪o W) :
    tupleVertices (f.trans g.toEmbedding) =
      (tupleVertices f).image g := by
  ext v
  simp only [tupleVertices, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨f x, ⟨x, rfl⟩, hx⟩
  · rintro ⟨x, ⟨y, hy⟩, hx⟩
    exact ⟨y, by simpa [← hy] using hx⟩

/-- Importantly, preserving the table of signs on subsets is
sufficient to preserve the intrinsic hypertournament orientation
for every injective ordered tuple. -/
theorem fromOrderedSigns_preserves {n : ℕ} {V W : Type*}
    [LinearOrder V] [LinearOrder W]
    (g : V ↪o W)
    (s : Finset V → Bool) (t : Finset W → Bool)
    (h : ∀ Q : Finset V, t (Q.image g) = s Q) :
    Preserves (Hyper.fromOrderedSigns (n := n) s)
              (Hyper.fromOrderedSigns (n := n) t) g.toEmbedding := by
  intro f
  change orderedSignOrientation t (f.trans g.toEmbedding) =
    orderedSignOrientation s f
  unfold orderedSignOrientation
  rw [sort_map_orderEmbedding f g, tupleVertices_map_orderEmbedding f g,
      h (tupleVertices f)]

end Hypertournaments
