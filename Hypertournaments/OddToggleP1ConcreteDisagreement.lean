import Hypertournaments.OddToggleP1SideDisagreement

/-!
# Explicit actual common n-tuple on which the p1 sides disagree

The finite source/side sign tables differ on omitted old core pair
a2,a4. Here the relevant (4k+5)-vertex side n-set is constructed as
the full one-point universe after removing exactly those two
canonical old vertices. Its cardinality, presence of the new
endpoint and exact old missing set are proved, not assumed.

Consequently the *actual intrinsic* two one-point sides have
different n-ary orientations on a common old-indexed tuple. This
rules out identifying their new vertices in ordinary amalgams;
the separate distinct-vertex obstruction is still required.
-/

namespace Hypertournaments

/-- The canonical side n-subset obtained by omitting core vertices
a2 and a4 while retaining the last (new) vertex. -/
def p1Core24FacetSet (k : ℕ) : Finset (Fin (4*k+6+1)) :=
  ((Finset.univ : Finset (Fin (4*k+6+1))).erase
      (p1CoreAt k (2 : Fin 6)).castSucc).erase
      (p1CoreAt k (4 : Fin 6)).castSucc

/-- This is a real n-element vertex subset in the side structure. -/
theorem p1Core24Facet_card (k : ℕ) :
    (p1Core24FacetSet k).card = 4*k+5 := by
  let v : Fin (4*k+6) := p1CoreAt k (2 : Fin 6)
  let w : Fin (4*k+6) := p1CoreAt k (4 : Fin 6)
  have hvw : v ≠ w := ne_of_lt (p1CoreAt_two_lt_four k)
  have hfirst :
      ((Finset.univ : Finset (Fin (4*k+6+1))).erase
        v.castSucc).card + 1 = 4*k+6+1 := by
    have h := Finset.card_erase_add_one
      (Finset.mem_univ (v.castSucc : Fin (4*k+6+1)))
    simpa using h
  have hsecond :
      (((Finset.univ : Finset (Fin (4*k+6+1))).erase
        v.castSucc).erase w.castSucc).card + 1 =
      ((Finset.univ : Finset (Fin (4*k+6+1))).erase
        v.castSucc).card := by
    have hmem :
        (w.castSucc : Fin (4*k+6+1)) ∈
          (Finset.univ : Finset (Fin (4*k+6+1))).erase v.castSucc := by
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro he
      exact hvw ((Fin.castSuccEmb : Fin (4*k+6) ↪
        Fin (4*k+6+1)).injective he.symm)
    simpa using Finset.card_erase_add_one hmem
  change (((Finset.univ : Finset (Fin (4*k+6+1))).erase
      v.castSucc).erase w.castSucc).card = 4*k+5
  omega

/-- The new endpoint belongs to the distinguished side facet. -/
theorem p1Core24Facet_last_mem (k : ℕ) :
    Fin.last (4*k+6) ∈ p1Core24FacetSet k := by
  have hneq (v : Fin (4*k+6)) :
      Fin.last (4*k+6) ≠ (v.castSucc : Fin (4*k+6+1)) := by
    intro he
    have h := congrArg Fin.val he
    simp only [Fin.val_last, Fin.val_castSucc] at h
    have hv := v.isLt
    omega
  exact Finset.mem_erase.mpr
    ⟨hneq (p1CoreAt k (4 : Fin 6)),
      Finset.mem_erase.mpr
        ⟨hneq (p1CoreAt k (2 : Fin 6)), Finset.mem_univ _⟩⟩

/-- Exactly a2 and a4 are absent from the base part. -/
theorem p1Core24Facet_missing (k : ℕ) :
    p1MissingBase k (p1Core24FacetSet k) =
      ({p1CoreAt k (2 : Fin 6), p1CoreAt k (4 : Fin 6)} :
        Finset (Fin (4*k+6))) := by
  let v : Fin (4*k+6) := p1CoreAt k (2 : Fin 6)
  let w : Fin (4*k+6) := p1CoreAt k (4 : Fin 6)
  have hcast (x y : Fin (4*k+6)) :
      (x.castSucc : Fin (4*k+6+1)) = y.castSucc ↔ x=y := by
    constructor
    · intro h
      exact (Fin.castSuccEmb : Fin (4*k+6) ↪
        Fin (4*k+6+1)).injective h
    · intro h
      rw [h]
  ext x
  have hmem :
      (x.castSucc : Fin (4*k+6+1)) ∈ p1Core24FacetSet k ↔
        x ≠ v ∧ x ≠ w := by
    simp [p1Core24FacetSet, v, w, hcast, and_comm]
  simp only [p1MissingBase, Finset.mem_filter, Finset.mem_univ,
    true_and]
  change (x.castSucc : Fin (4*k+6+1)) ∉
      p1Core24FacetSet k ↔ x ∈ ({v,w} : Finset (Fin (4*k+6)))
  rw [hmem]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- **Actual** intrinsic n-tuple witnessing disagreement between
the two one-point sides. -/
theorem p1ConcreteSides_orient_disagreement (k : ℕ) :
    ∃ t : Fin (4*k+5) ↪ Fin (4*k+6+1),
      (p1SideHyper k true).orient t ≠
        (p1SideHyper k false).orient t := by
  let Q := p1Core24FacetSet k
  have hQ : Q.card = 4*k+5 := p1Core24Facet_card k
  refine ⟨(Q.orderEmbOfFin hQ).toEmbedding, ?_⟩
  exact p1SideHyper_core_24_orient_disagree k Q hQ
    (p1Core24Facet_last_mem k) (p1Core24Facet_missing k)

end Hypertournaments
