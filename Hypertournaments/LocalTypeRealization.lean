import Hypertournaments.CanonicalPacket

/-!
# Realizing every normalized local packet and local type

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`lem:local-type-isomorphism`. Canonical facets are independently prescribed,
then extended by alternation using the shared ordered-sign presentation.
-/

namespace Hypertournaments

/-- Interpret a normalized packet as a canonical sign table. Only the
one-point-complement case is used for the n-element facets. -/
def normalizedPacketSigns {n : ℕ} (bits : Fin (n + 1) → Bool)
    (Q : Finset (Fin (n + 1))) : Bool :=
  if h : Qᶜ.Nonempty then
    Bool.xor (bits (Qᶜ.min' h)) (decide ((Qᶜ.min' h).val % 2 = 1))
  else false

@[simp] theorem normalizedPacketSigns_univ_erase {n : ℕ}
    (bits : Fin (n + 1) → Bool) (i : Fin (n + 1)) :
    normalizedPacketSigns bits (Finset.univ.erase i) =
      Bool.xor (bits i) (decide (i.val % 2 = 1)) := by
  simp [normalizedPacketSigns]

/-- The actual intrinsic hypertournament realizing any normalized packet. -/
def Hyper.fromNormalizedPacket {n : ℕ} (bits : Fin (n + 1) → Bool) :
    Hyper n (Fin (n + 1)) := Hyper.fromOrderedSigns (normalizedPacketSigns bits)

/-- Its canonical raw facet orientations have exactly the prescribed parity correction. -/
theorem fromNormalizedPacket_facet {n : ℕ} (bits : Fin (n + 1) → Bool)
    (i : Fin (n + 1)) :
    (Hyper.fromNormalizedPacket bits).orient
      (facet (Function.Embedding.refl (Fin (n + 1))) i) =
      Bool.xor (bits i) (decide (i.val % 2 = 1)) := by
  change (Hyper.fromOrderedSigns (normalizedPacketSigns bits)).orient _ = _
  rw [fromOrderedSigns_orient_strictMono _ _ (Fin.strictMono_succAbove i)]
  rw [tupleVertices_facet_eq_erase]
  have hv : tupleVertices (Function.Embedding.refl (Fin (n + 1))) = Finset.univ := by
    change Finset.image id Finset.univ = Finset.univ
    exact Finset.image_id
  rw [hv, normalizedPacketSigns_univ_erase]
  rfl

/-- Normalizing the actual canonical facets recovers the arbitrary input packet. -/
@[simp] theorem normalizedFacet_fromNormalizedPacket {n : ℕ}
    (bits : Fin (n + 1) → Bool) (i : Fin (n + 1)) :
    normalizedFacet (Hyper.fromNormalizedPacket bits)
      (Function.Embedding.refl (Fin (n + 1))) i = bits i := by
  unfold normalizedFacet
  rw [fromNormalizedPacket_facet]
  cases bits i <;> cases decide (i.val % 2 = 1) <;> rfl

/-- Counting normalized facets of the realized packet is exactly counting its bits. -/
theorem positiveFacetCount_fromNormalizedPacket {n : ℕ}
    (bits : Fin (n + 1) → Bool) :
    positiveFacetCount (Hyper.fromNormalizedPacket bits)
      (Function.Embedding.refl (Fin (n + 1))) =
      (Finset.univ.filter (fun i => bits i = true)).card := by
  simp only [positiveFacetCount, normalizedFacet_fromNormalizedPacket]

/-- A canonical representative of type d: precisely its first d normalized
facet bits are true. The bound on d is needed only for the type theorem. -/
def localTypeRepresentative (n d : ℕ) : Hyper n (Fin (n + 1)) :=
  Hyper.fromNormalizedPacket (fun i => decide (i.val < d))

theorem positiveFacetCount_localTypeRepresentative (n d : ℕ) (hd : d ≤ n + 1) :
    positiveFacetCount (localTypeRepresentative n d)
      (Function.Embedding.refl (Fin (n + 1))) = d := by
  rw [localTypeRepresentative, positiveFacetCount_fromNormalizedPacket]
  simp only [decide_eq_true_eq, Fin.card_filter_val_lt, Nat.min_eq_right hd]

/-- Every actual local type index up to the central type is realized,
including the low-arity edge cases. -/
theorem localIndex_localTypeRepresentative (n d : ℕ) (hd : d ≤ centralIndex n) :
    localIndex (localTypeRepresentative n d)
      (Function.Embedding.refl (Fin (n + 1))) = d := by
  have hbound : d ≤ n + 1 := by unfold centralIndex at hd; omega
  unfold localIndex
  rw [positiveFacetCount_localTypeRepresentative n d hbound]
  apply Nat.min_eq_left
  unfold centralIndex at hd
  omega

/-- Existential formulation with an actual intrinsic finite hypertournament. -/
theorem exists_localIndex_eq {n d : ℕ} (hd : d ≤ centralIndex n) :
    ∃ A : Hyper n (Fin (n + 1)),
      localIndex A (Function.Embedding.refl (Fin (n + 1))) = d :=
  ⟨localTypeRepresentative n d, localIndex_localTypeRepresentative n d hd⟩

end Hypertournaments
