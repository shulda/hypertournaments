import Hypertournaments.FiveConstrained.CatalogueIsomorphism

/-!
# The classification supplement's positive-sign catalogue

Source: `tex_hypertournaments` at
`64a392aa2b0e497c297f1218be3f1a8761bae18d`, `tab:five-types` and
`app:formalization`. The supplement records positive increasing triples by
bits equal to one, whereas `maskHyper` stores the literal Boolean orientation
and positive orientation is `false`. Its displayed mask must be complemented.
This exchanges two pairs of individual catalogue labels but preserves every
positive classification palette.
-/

namespace Hypertournaments.FiveConstrained

/-- Translate the supplement's positive-sign labels to the raw Lean catalogue. -/
def sourceTypeToLean (i : Fin 12) : Fin 12 :=
  #[0, 1, 2, 7, 4, 5, 6, 3, 8, 9, 11, 10][i.val]!

/-- Applying the change of sign convention twice restores the original label. -/
theorem sourceTypeToLean_involutive : Function.Involutive sourceTypeToLean := by
  change ∀ i : Fin 12, sourceTypeToLean (sourceTypeToLean i) = i
  decide

@[simp] theorem sourceTypeToLean_p9 : sourceTypeToLean 9 = 9 := rfl

/-- The supplement's displayed positive-sign mask has this actual Lean label. -/
theorem type5_source_positive_mask (i : Fin 12) :
    type5 (Nat.xor 1023 (representative i)) = sourceTypeToLean i := by
  have h : ∀ i : Fin 12,
      type5 (Nat.xor 1023 (representative i)) = sourceTypeToLean i := by decide
  exact h i

/-- The actual intrinsic hypertournament specified by the supplement's table. -/
def sourcePositiveRepresentative (i : Fin 12) : Hyper 3 (Fin 5) :=
  maskHyper 5 (Nat.xor 1023 (representative i))

/-- A listed positive triple has orientation `false`; an unlisted one has
orientation `true`, on each of the ten increasing triples. -/
theorem sourcePositiveRepresentative_triple5 (i : Fin 12) (j : Fin 10) :
    (sourcePositiveRepresentative i).orient (triple5 j) =
      !(representative i).testBit j.val := by
  have h : ∀ (i : Fin 12) (j : Fin 10),
      (sourcePositiveRepresentative i).orient (triple5 j) =
        !(representative i).testBit j.val := by decide
  exact h i j

theorem sourcePositiveRepresentative_type5 (i : Fin 12) :
    type5 (encode5 (sourcePositiveRepresentative i)) = sourceTypeToLean i := by
  have hbound : Nat.xor 1023 (representative i) < 1024 := by
    have h : ∀ i : Fin 12, Nat.xor 1023 (representative i) < 1024 := by decide
    exact h i
  unfold sourcePositiveRepresentative
  rw [encode5_maskHyper ⟨_, hbound⟩]
  exact type5_source_positive_mask i

/-- The dictionary is witnessed by an actual orientation-preserving vertex
permutation, rather than by equality of an unrelated numerical label. -/
theorem sourcePositiveRepresentative_isomorphic (i : Fin 12) :
    ∃ σ : Equiv.Perm (Fin 5),
      Preserves (maskHyper 5 (representative (sourceTypeToLean i)))
        (sourcePositiveRepresentative i) σ.toEmbedding := by
  exact (representative_iso_iff_type5 _ _).mpr (sourcePositiveRepresentative_type5 i)

/-- The change of convention leaves the induced four-type supports unchanged. -/
theorem sourceTypeToLean_support4 (i : Fin 12) :
    support4 (sourceTypeToLean i) = support4 i := by
  have h : ∀ i : Fin 12, support4 (sourceTypeToLean i) = support4 i := by decide
  exact h i

/-- Every one of the five positive classification palettes is invariant
under the change from positive-sign labels to literal Boolean labels. -/
theorem sourceTypeToLean_positive_palette (p : Fin 5) (i : Fin 12) :
    (#[1, 119, 257, 3583, 4095][p.val]! : ℕ).testBit (sourceTypeToLean i).val =
      (#[1, 119, 257, 3583, 4095][p.val]! : ℕ).testBit i.val := by
  have h : ∀ (p : Fin 5) (i : Fin 12),
      (#[1, 119, 257, 3583, 4095][p.val]! : ℕ).testBit (sourceTypeToLean i).val =
        (#[1, 119, 257, 3583, 4095][p.val]! : ℕ).testBit i.val := by decide
  exact h p i

end Hypertournaments.FiveConstrained
