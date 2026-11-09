import Hypertournaments.LocalTypes

/-!
# Uniform restriction of a vertex transposition to a facet

For any arity, swapping two tuple coordinates *other than* the
coordinate being deleted induces a swap of the two corresponding
facet coordinates. This is the key generic geometric fact behind
the normalized-facet relabeling law.

Unlike arity-four/five lookup tables, these statements hold for
arbitrary n and need no case enumeration.
-/

namespace Hypertournaments

/-- A transposition on Fin(n+1), avoiding pivot k, descends to
a transposition on Fin n via the injection k.succAbove. -/
theorem exists_restricted_swap
    {n : ℕ} (k a b : Fin (n + 1))
    (hka : k ≠ a) (hkb : k ≠ b) (hab : a ≠ b) :
    ∃ u v : Fin n, u ≠ v ∧
      ∀ i : Fin n,
        (Equiv.swap a b) (k.succAbove i) =
          k.succAbove ((Equiv.swap u v) i) := by
  obtain ⟨u, hu⟩ : ∃ u : Fin n, k.succAbove u = a :=
    Fin.exists_succAbove_eq hka.symm
  obtain ⟨v, hv⟩ : ∃ v : Fin n, k.succAbove v = b :=
    Fin.exists_succAbove_eq hkb.symm
  have huv : u ≠ v := by
    intro he
    apply hab
    calc
      a = k.succAbove u := hu.symm
      _ = k.succAbove v := congrArg k.succAbove he
      _ = b := hv
  refine ⟨u, v, huv, ?_⟩
  intro i
  have hinj : Function.Injective k.succAbove :=
    Fin.succAbove_right_injective
  calc
    (Equiv.swap a b) (k.succAbove i) =
        (Equiv.swap (k.succAbove u) (k.succAbove v)) (k.succAbove i) := by
      rw [hu, hv]
    _ = k.succAbove ((Equiv.swap u v) i) :=
      hinj.swap_apply u v i

/-- Any swap avoiding deleted coordinate k reverses the raw facet
orientation, in any arity. -/
theorem orient_facet_swap_away
    {n : ℕ} {V : Type*} (A : Hyper n V)
    (f : Fin (n + 1) ↪ V)
    (a b k : Fin (n + 1))
    (hka : k ≠ a) (hkb : k ≠ b) (hab : a ≠ b) :
    A.orient (facet ((Equiv.swap a b).toEmbedding.trans f) k) =
      !(A.orient (facet f k)) := by
  obtain ⟨u, v, huv, hcoord⟩ :=
    exists_restricted_swap k a b hka hkb hab
  have hemb :
      facet ((Equiv.swap a b).toEmbedding.trans f) k =
        (Equiv.swap u v).toEmbedding.trans (facet f k) := by
    ext i
    change f ((Equiv.swap a b) (k.succAbove i)) =
      f (k.succAbove ((Equiv.swap u v) i))
    exact congrArg f (hcoord i)
  rw [hemb]
  exact A.swap_flip (facet f k) u v huv

/-- Away from both swapped coordinates, the normalized facet sign
is complemented (no index shift occurs). -/
theorem normalizedFacet_swap_away
    {n : ℕ} {V : Type*} (A : Hyper n V)
    (f : Fin (n + 1) ↪ V)
    (a b k : Fin (n + 1))
    (hka : k ≠ a) (hkb : k ≠ b) (hab : a ≠ b) :
    normalizedFacet A ((Equiv.swap a b).toEmbedding.trans f) k =
      !(normalizedFacet A f k) := by
  unfold normalizedFacet
  rw [orient_facet_swap_away A f a b k hka hkb hab]
  cases hraw : A.orient (facet f k) <;>
    cases hpar : decide (k.val % 2 = 1) <;> decide

end Hypertournaments
