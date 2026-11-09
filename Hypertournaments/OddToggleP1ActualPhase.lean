import Hypertournaments.OddToggleP1DoubleFacet
import Hypertournaments.OddToggleP1RawAlternating
import Hypertournaments.OddToggleP1ZeroTwoAbstract

/-!
# Actual homogeneous deleted facets satisfy the abstract phase premise

For any increasing packet f with n+2 vertices, the i-th deleted
(n+1)-packet is itself canonically increasing. If its local type is
zero, its raw n-facets alternate in the deletion index t.

Our exact succAbove position lemma identifies t with j before i,
and j-1 after i. Since double erasure of finite vertex sets is exact,
the raw sign of the twice-deleted facet is therefore the abstract
phase(i) xor parity(p1ErasePosition i j) of the zero-or-two theorem.

This is a genuine intrinsic hypertournament statement, with no
assumption about the allowed type family or amalgamation.
-/

namespace Hypertournaments

/-- An increasing facet of an increasing tuple, retained as a
strictly monotone order embedding. -/
def p1OrderedFacet {n a : ℕ}
    (f : Fin (n+2) ↪o Fin a) (i : Fin (n+2)) :
    Fin (n+1) ↪o Fin a :=
  OrderEmbedding.ofStrictMono (facet f.toEmbedding i)
    (f.strictMono.comp (Fin.strictMono_succAbove i))

theorem p1OrderedFacet_toEmbedding {n a : ℕ}
    (f : Fin (n+2) ↪o Fin a) (i : Fin (n+2)) :
    (p1OrderedFacet f i).toEmbedding = facet f.toEmbedding i := by
  ext j
  rfl

/-- Under any injective map, image of an erased finite set is
the erased image. No cardinality hypothesis is needed. -/
theorem p1ImageErase {r a : ℕ}
    (f : Fin r ↪ Fin a) (Q : Finset (Fin r)) (i : Fin r) :
    (Q.erase i).image f = (Q.image f).erase (f i) := by
  ext v
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨x, ⟨hxi, hxQ⟩, hxv⟩
    refine ⟨?_, ⟨x, hxQ, hxv⟩⟩
    intro hvi
    apply hxi
    exact f.injective (hxv.trans hvi.symm)
  · rintro ⟨hvi, ⟨x, hxQ, hxv⟩⟩
    refine ⟨x, ⟨?_, hxQ⟩, hxv⟩
    intro hxi
    subst x
    exact hvi hxv.symm

/-- The canonical source sign on doubly erased index sets is the
same genuine source n-facet sign as deleting the original vertices
in either order. -/
theorem p1DoubleErase_image
    {n a : ℕ} (f : Fin (n+2) ↪o Fin a)
    (i j : Fin (n+2)) :
    ((((Finset.univ : Finset (Fin (n+2))).erase i).erase j).image
      f.toEmbedding) =
      ((tupleVertices f.toEmbedding).erase (f i)).erase (f j) := by
  calc
    (((((Finset.univ : Finset (Fin (n+2))).erase i).erase j).image
        f.toEmbedding) =
      (((Finset.univ : Finset (Fin (n+2))).erase i).image
        f.toEmbedding).erase (f j) :=
      p1ImageErase f.toEmbedding _ j
    _ = ((tupleVertices f.toEmbedding).erase (f i)).erase (f j) := by
      rw [p1ImageErase f.toEmbedding (Finset.univ : Finset (Fin (n+2))) i]
      rfl

/-- For each actually homogeneous deleted packet, an alternating
raw phase exists for every original second deletion j. -/
theorem Hyper.p1ActualPhase_family
    {n a : ℕ} (A : Hyper n (Fin a))
    (f : Fin (n+2) ↪o Fin a) :
    ∃ phase : Fin (n+2) → Bool,
      ∀ i : Fin (n+2),
        localIndex A (facet f.toEmbedding i) = 0 →
        ∀ j : Fin (n+2), j ≠ i →
          A.canonicalSignTable
            (((((Finset.univ : Finset (Fin (n+2))).erase i).erase j)
              .image f.toEmbedding)) =
            (phase i ^^ decide ((p1ErasePosition i j)%2=1)) := by
  classical
  let H : Fin (n+2) → Prop :=
    fun i => localIndex A (facet f.toEmbedding i) = 0
  have hphase (i : Fin (n+2)) (hi : H i) :
      ∃ b : Bool, ∀ t : Fin (n+1),
        A.canonicalSignTable
          (tupleVertices (facet (facet f.toEmbedding i) t)) =
          (b ^^ decide (t.val%2=1)) := by
    let g : Fin (n+1) ↪o Fin a := p1OrderedFacet f i
    have hg : g.toEmbedding = facet f.toEmbedding i :=
      p1OrderedFacet_toEmbedding f i
    have hgzero : localIndex A g.toEmbedding = 0 := by
      rw [hg]
      exact hi
    obtain ⟨b, hb⟩ :=
      A.localIndex_zero_canonical_sign_alternating g hgzero
    refine ⟨b, ?_⟩
    intro t
    simpa only [hg] using hb t
  let phase : Fin (n+2) → Bool :=
    fun i => if hi : H i then Classical.choose (hphase i hi) else false
  refine ⟨phase, ?_⟩
  intro i hi j hji
  obtain ⟨t, ht, hindex, hverts⟩ :=
    p1ActualDoubleFacet_vertices f i j hji.symm
  have hphaseEq : phase i = Classical.choose (hphase i hi) := by
    dsimp [phase]
    simp [hi]
  calc
    A.canonicalSignTable
        (((((Finset.univ : Finset (Fin (n+2))).erase i).erase j)
          .image f.toEmbedding)) =
      A.canonicalSignTable
        (tupleVertices (facet (facet f.toEmbedding i) t)) := by
          rw [p1DoubleErase_image f i j, ← hverts]
    _ = (Classical.choose (hphase i hi) ^^ decide (t.val%2=1)) :=
      (Classical.choose_spec (hphase i hi)) t
    _ = (phase i ^^ decide ((p1ErasePosition i j)%2=1)) := by
      rw [hphaseEq, hindex]

/-- There cannot be three homogeneous (n+1)-subpackets inside
any actual (n+2)-vertex hypertournament packet, at any arity.
This is the geometric phase half of the zero-or-two principle. -/
theorem Hyper.p1ActualHomogeneous_card_le_two
    {n a : ℕ} (A : Hyper n (Fin a))
    (f : Fin (n+2) ↪o Fin a) :
    (Finset.univ.filter (fun i : Fin (n+2) =>
      localIndex A (facet f.toEmbedding i) = 0)).card ≤ 2 := by
  classical
  obtain ⟨phase, hphase⟩ := A.p1ActualPhase_family f
  exact p1RawHomogeneous_card_le_two n
    (fun Q => A.canonicalSignTable (Q.image f.toEmbedding))
    (fun i => localIndex A (facet f.toEmbedding i) = 0)
    phase (by
      intro i hi j hji
      exact hphase i hi j hji)

end Hypertournaments
