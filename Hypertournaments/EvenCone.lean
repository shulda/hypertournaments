import Hypertournaments.EvenPotential
import Hypertournaments.CanonicalPacket
import Mathlib.Data.Finset.Preimage
import Hypertournaments.OnePointLink
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Ext

/-!
# Even cones over lower-arity hypertournaments

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`prop:even-eppa-transfer`. A new root has the original orientation as
its link, and the orientation away from the root is its coboundary.
-/

namespace Hypertournaments

universe u

noncomputable section

/-- Canonical potential signs: zero on subsets containing the new least
vertex, and the original signs on subsets of old vertices. -/
def conePotentialSigns {r a : ℕ} (A : Hyper r (Fin a))
    (Q : Finset (Fin (a + 1))) : Bool :=
  if 0 ∈ Q then false else
    A.canonicalSignTable (Q.preimage (Fin.succEmb a) (Fin.succEmb a).injective.injOn)

def Hyper.conePotentialFin {r a : ℕ} (A : Hyper r (Fin a)) :
    Hyper r (Fin (a + 1)) := Hyper.fromOrderedSigns (conePotentialSigns A)

theorem conePotentialSigns_old {r a : ℕ} (A : Hyper r (Fin a)) (Q : Finset (Fin a)) :
    conePotentialSigns A (Q.image (Fin.succOrderEmb a)) = A.canonicalSignTable Q := by
  have hmap : Q.image (Fin.succOrderEmb a) = Q.map (Fin.succEmb a) := by
    ext x
    simp
  rw [hmap]
  have hzero : (0 : Fin (a + 1)) ∉ Q.map (Fin.succEmb a) := by
    simp [Fin.succEmb]
  simp only [conePotentialSigns, hzero, ↓reduceIte]
  rw [Finset.preimage_map]

/-- The potential on all old tuples is literally the original orientation. -/
theorem Hyper.conePotentialFin_old {r a : ℕ} (A : Hyper r (Fin a)) :
    Preserves A A.conePotentialFin (Fin.succEmb a) := by
  have h := fromOrderedSigns_preserves (n := r) (Fin.succOrderEmb a)
    A.canonicalSignTable (conePotentialSigns A) (conePotentialSigns_old A)
  intro t
  exact (h t).trans (A.from_canonicalSignTable_orient t)

/-- The finite ordinal cone is the coboundary of the chosen potential. -/
def Hyper.evenConeFin {r a : ℕ} (A : Hyper r (Fin a)) (hr : Even r) :
    Hyper (r + 1) (Fin (a + 1)) := A.conePotentialFin.coboundary hr

theorem Hyper.evenConeFin_isEven {r a : ℕ} (A : Hyper r (Fin a)) (hr : Even r) :
    (A.evenConeFin hr).IsEven := A.conePotentialFin.isEven_coboundary hr

/-- Restriction of the cone to old vertices is the intrinsic coboundary. -/
theorem Hyper.evenConeFin_old {r a : ℕ} (A : Hyper r (Fin a)) (hr : Even r) :
    Preserves (A.coboundary hr) (A.evenConeFin hr) (Fin.succEmb a) :=
  A.coboundary_preserves A.conePotentialFin hr (Fin.succEmb a) A.conePotentialFin_old

theorem finZero_not_mem_succRange (a : ℕ) :
    (0 : Fin (a + 1)) ∉ Set.range (Fin.succEmb a) := by
  simp [Fin.succEmb]

theorem onePointTuple_fin_strictMono {r a : ℕ} (t : Fin r ↪o Fin a) :
    StrictMono (onePointTuple (Fin.succEmb a) 0 (finZero_not_mem_succRange a)
      t.toEmbedding) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro h
      exact (lt_irrefl _ h).elim
    · intro _
      exact Fin.succ_pos _
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro h
      exact (not_lt_of_ge (Fin.zero_le _) h).elim
    · intro h
      change (t i).succ < (t j).succ
      exact Fin.succ_lt_succ_iff.mpr (t.strictMono (Fin.succ_lt_succ_iff.mp h))

theorem Hyper.evenConeFin_root_canonical {r a : ℕ}
    (A : Hyper r (Fin a)) (hr : Even r) (t : Fin r ↪o Fin a) :
    (A.evenConeFin hr).orient
      (onePointTuple (Fin.succEmb a) 0 (finZero_not_mem_succRange a) t.toEmbedding) =
      A.orient t.toEmbedding := by
  let f := onePointTuple (Fin.succEmb a) 0 (finZero_not_mem_succRange a) t.toEmbedding
  let fo : Fin (r + 1) ↪o Fin (a + 1) :=
    OrderEmbedding.ofStrictMono f (onePointTuple_fin_strictMono t)
  have hzero : facet f 0 = t.toEmbedding.trans (Fin.succEmb a) := by
    ext j
    rfl
  have htail (i : Fin r) : A.conePotentialFin.orient (facet f i.succ) = false := by
    change (Hyper.fromOrderedSigns (conePotentialSigns A)).orient
      (facet fo.toEmbedding i.succ) = false
    rw [fromOrderedSigns_facet_increasing]
    have hz : (0 : Fin (a + 1)) ∈ tupleVertices (facet f i.succ) := by
      rw [tupleVertices_facet_eq_erase]
      refine Finset.mem_erase.mpr ⟨?_, ?_⟩
      · intro he
        have hcoord : (0 : Fin (r + 1)) = i.succ := f.injective he
        exact (Fin.succ_ne_zero i) hcoord.symm
      · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
    exact ite_eq_left hz
  apply p1BitToZMod_injective
  change p1BitToZMod ((A.conePotentialFin.coboundary hr).orient f) = _
  rw [Hyper.coboundary_orient]
  unfold tupleCoboundary
  rw [Fin.sum_univ_succ]
  change p1BitToZMod (A.conePotentialFin.orient (facet f 0)) +
    (∑ i : Fin r, p1BitToZMod (A.conePotentialFin.orient (facet f i.succ))) = _
  rw [hzero, A.conePotentialFin_old t.toEmbedding]
  simp only [htail, p1BitToZMod, Bool.false_eq_true, ↓reduceIte,
    Finset.sum_const_zero, add_zero]

/-- The root link recovers the original orientation on arbitrary old tuples. -/
theorem Hyper.evenConeFin_root_orient {r a : ℕ}
    (A : Hyper r (Fin a)) (hr : Even r) (t : Fin r ↪ Fin a) :
    (A.evenConeFin hr).orient
      (onePointTuple (Fin.succEmb a) 0 (finZero_not_mem_succRange a) t) =
      A.orient t := by
  exact orientations_equal_of_canonical
    ((A.evenConeFin hr).onePointSlice (Fin.succEmb a) 0 (finZero_not_mem_succRange a)) A
    (fun Q hQ => A.evenConeFin_root_canonical hr (Q.orderEmbOfFin hQ)) t

/-- A finite carrier is enumerated only to construct the cone; the final
root and old-tuple equations are independent of that enumeration. -/
def finiteConeIndex (V : Type u) [Finite V] : V ≃ Fin (Nat.card V) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  exact Fintype.equivFinOfCardEq (by simp only [Nat.card_eq_fintype_card])

def optionConeIndex (V : Type u) [Finite V] : Option V ≃ Fin (Nat.card V + 1) :=
  (Equiv.optionCongr (finiteConeIndex V)).trans (finSuccEquiv (Nat.card V)).symm

@[simp] theorem optionConeIndex_none (V : Type u) [Finite V] :
    optionConeIndex V none = 0 := by simp [optionConeIndex]

@[simp] theorem optionConeIndex_some (V : Type u) [Finite V] (x : V) :
    optionConeIndex V (some x) = (finiteConeIndex V x).succ := by
  simp [optionConeIndex]

theorem none_not_mem_someRange (V : Type u) :
    (none : Option V) ∉ Set.range (Function.Embedding.some : V ↪ Option V) := by
  rintro ⟨x, h⟩
  exact Option.some_ne_none x h

/-- The even one-point cone on a finite hypertournament. -/
def Hyper.evenCone {r : ℕ} {V : Type u} [Finite V]
    (A : Hyper r V) (hr : Even r) : Hyper (r + 1) (Option V) :=
  ((A.pullback (finiteConeIndex V).symm.toEmbedding).evenConeFin hr).pullback
    (optionConeIndex V).toEmbedding

theorem Hyper.evenCone_isEven {r : ℕ} {V : Type u} [Finite V]
    (A : Hyper r V) (hr : Even r) : (A.evenCone hr).IsEven :=
  ((A.pullback (finiteConeIndex V).symm.toEmbedding).evenConeFin_isEven hr).pullback _

/-- The cone's restriction to old vertices is the original coboundary. -/
theorem Hyper.evenCone_old_orient {r : ℕ} {V : Type u} [Finite V]
    (A : Hyper r V) (hr : Even r) (t : Fin (r + 1) ↪ V) :
    (A.evenCone hr).orient (t.trans Function.Embedding.some) =
      (A.coboundary hr).orient t := by
  let s := finiteConeIndex V
  have ht : (t.trans Function.Embedding.some).trans (optionConeIndex V).toEmbedding =
      (t.trans s.toEmbedding).trans (Fin.succEmb (Nat.card V)) := by
    apply Function.Embedding.ext
    intro i
    exact optionConeIndex_some V (t i)
  change ((A.pullback s.symm.toEmbedding).evenConeFin hr).orient _ = _
  rw [ht, Hyper.evenConeFin_old, Hyper.coboundary_pullback]
  change (A.coboundary hr).orient ((t.trans s.toEmbedding).trans s.symm.toEmbedding) = _
  congr 1
  ext i
  exact s.symm_apply_apply _

/-- The link of the distinguished root is the given lower orientation. -/
theorem Hyper.evenCone_root_orient {r : ℕ} {V : Type u} [Finite V]
    (A : Hyper r V) (hr : Even r) (t : Fin r ↪ V) :
    (A.evenCone hr).orient
      (onePointTuple Function.Embedding.some none (none_not_mem_someRange V) t) =
        A.orient t := by
  let s := finiteConeIndex V
  have ht :
      (onePointTuple Function.Embedding.some none (none_not_mem_someRange V) t).trans
          (optionConeIndex V).toEmbedding =
        onePointTuple (Fin.succEmb (Nat.card V)) 0 (finZero_not_mem_succRange _)
          (t.trans s.toEmbedding) := by
    apply Function.Embedding.ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact optionConeIndex_none V
    · exact optionConeIndex_some V (t j)
  change ((A.pullback s.symm.toEmbedding).evenConeFin hr).orient _ = _
  rw [ht, Hyper.evenConeFin_root_orient]
  change A.orient ((t.trans s.toEmbedding).trans s.symm.toEmbedding) = _
  congr 1
  ext i
  exact s.symm_apply_apply _

end

end Hypertournaments
