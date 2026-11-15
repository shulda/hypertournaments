import Hypertournaments.LocalPairCancellation
import Hypertournaments.OnePointLink
import Hypertournaments.Antichain.HomogeneousPacket
import Hypertournaments.StrictConstraint.OnePointGlue

/-!
# Adding one vertex to a pair-cancelling hypertournament

A prescribed root link is enough: every old vertex belongs to a homogeneous
packet of that link, so its new pair has two different orientations under
every auxiliary order. Old pairs retain their existing witnesses.

Source: `tex_hypertournaments`, commit
`64a392aa2b0e497c297f1218be3f1a8761bae18d`,
`obs:strict-constrained-hierarchy`.
-/

namespace Hypertournaments.StrictConstraint

private def PairWitness {n : ℕ} {V : Type*} (A : Hyper n V)
    (order : LinearOrder V) (u v : V) : Prop :=
  ∃ f g : Fin n ↪ V, @IsPairLink n V order u v f ∧
    @IsPairLink n V order u v g ∧ A.orient f ≠ A.orient g

private theorem pairWitness_symm {n : ℕ} {V : Type*} (hn : 2 ≤ n)
    (A : Hyper n V) (order : LinearOrder V) {u v : V}
    (h : PairWitness A order u v) : PairWitness A order v u := by
  let := order
  let z : Fin n := ⟨0, by omega⟩
  let o : Fin n := ⟨1, by omega⟩
  let σ := Equiv.swap z o
  have hzo : z ≠ o := by intro h; have := congrArg Fin.val h; simp [z, o] at this
  have hlink (f : Fin n ↪ V) (hf : IsPairLink u v f) :
      IsPairLink v u (σ.toEmbedding.trans f) := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      have hi' : i = z := Fin.ext hi
      subst i
      change f (σ z) = v
      rw [Equiv.swap_apply_left]
      exact hf.2.1 o rfl
    · intro i hi
      have hi' : i = o := Fin.ext hi
      subst i
      change f (σ o) = u
      rw [Equiv.swap_apply_right]
      exact hf.1 z rfl
    · intro i j hi hij
      have hiz : i ≠ z := by intro h; subst i; simp [z] at hi
      have hio : i ≠ o := by intro h; subst i; simp [o] at hi
      have hjz : j ≠ z := by intro h; subst j; change i.val < 0 at hij; omega
      have hjo : j ≠ o := by intro h; subst j; change i.val < 1 at hij; omega
      change f (σ i) < f (σ j)
      rw [Equiv.swap_apply_of_ne_of_ne hiz hio, Equiv.swap_apply_of_ne_of_ne hjz hjo]
      exact hf.2.2 i j hi hij
  obtain ⟨f, g, hf, hg, hfg⟩ := h
  refine ⟨σ.toEmbedding.trans f, σ.toEmbedding.trans g, hlink f hf, hlink g hg, ?_⟩
  rw [A.swap_flip f z o hzo, A.swap_flip g z o hzo]
  intro heq
  apply hfg
  simpa using congrArg Bool.not heq

private theorem old_pairWitness {n : ℕ} {V W : Type*}
    (A : Hyper n V) (B : Hyper n W) (e : V ↪ W)
    (hA : PairCancelling A) (he : Preserves A B e)
    (order : LinearOrder W) (u v : V) (huv : u ≠ v) :
    PairWitness B order (e u) (e v) := by
  let := order
  let oldOrder : LinearOrder V := LinearOrder.lift' e e.injective
  obtain ⟨f, g, hf, hg, hfg⟩ := hA.2.2 oldOrder u v huv
  have hlink (t : Fin n ↪ V) (ht : @IsPairLink n V oldOrder u v t) :
      IsPairLink (e u) (e v) (t.trans e) := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      exact congrArg e (ht.1 i hi)
    · intro i hi
      exact congrArg e (ht.2.1 i hi)
    · intro i j hi hij
      exact ht.2.2 i j hi hij
  refine ⟨f.trans e, g.trans e, hlink f hf, hlink g hg, ?_⟩
  simpa only [he f, he g] using hfg

/-- Enumerate a finite packet with one prescribed first point and increasing
remaining coordinates, without changing the packet's vertex set. -/
private theorem packet_first {r : ℕ} {V : Type*} [LinearOrder V]
    (f : Fin (r + 1) ↪ V) (v : V) (hv : v ∈ tupleVertices f) :
    ∃ g : Fin (r + 1) ↪ V, tupleVertices g = tupleVertices f ∧
      g 0 = v ∧ ∀ i j, 1 ≤ i.val → i < j → g i < g j := by
  classical
  let S := tupleVertices f
  let T := S.erase v
  have hS : S.card = r + 1 := by
    simp [S, tupleVertices, Finset.card_image_of_injective _ f.injective]
  have hT : T.card = r := by
    dsimp [T]
    rw [Finset.card_erase_of_mem hv]
    dsimp [S] at hS
    omega
  let e : Fin r ↪o V := T.orderEmbOfFin hT
  have he (i : Fin r) : e i ∈ T := Finset.orderEmbOfFin_mem T hT i
  have hout : v ∉ Set.range e.toEmbedding := by
    rintro ⟨i, hi⟩
    exact (Finset.mem_erase.mp (he i)).1 hi
  let g := Fin.Embedding.cons e.toEmbedding hout
  refine ⟨g, ?_, rfl, ?_⟩
  · ext x
    simp only [tupleVertices, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · exact (tupleVertices_mem_range f v).mp hv
      · exact (tupleVertices_mem_range f (e j)).mp (Finset.mem_erase.mp (he j)).2
    · rintro ⟨i, hi⟩
      by_cases hx : x = v
      · exact ⟨0, by simp [g, hx]⟩
      · have hxT : x ∈ T := Finset.mem_erase.mpr
          ⟨hx, (tupleVertices_mem_range f x).mpr ⟨i, hi⟩⟩
        have hxrange : x ∈ Set.range e := by
          simpa only [e, Finset.range_orderEmbOfFin, Finset.mem_coe] using hxT
        obtain ⟨j, hj⟩ := hxrange
        exact ⟨j.succ, hj⟩
  · intro i j hi hij
    obtain ⟨i', rfl⟩ : ∃ i' : Fin r, i = i'.succ :=
      ⟨⟨i.val - 1, by omega⟩, Fin.ext (by simp; omega)⟩
    obtain ⟨j', rfl⟩ : ∃ j' : Fin r, j = j'.succ :=
      ⟨⟨j.val - 1, by omega⟩, Fin.ext (by simp; omega)⟩
    apply e.strictMono
    change i'.val < j'.val
    change i'.val + 1 < j'.val + 1 at hij
    omega

private theorem facet_onePointTuple_succ {r : ℕ} {V W : Type*}
    (e : V ↪ W) (p : W) (hp : p ∉ Set.range e)
    (t : Fin (r + 1) ↪ V) (i : Fin (r + 1)) :
    facet (onePointTuple e p hp t) i.succ = onePointTuple e p hp (facet t i) := by
  ext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [facet, onePointTuple, Fin.succAbove, Fin.Embedding.cons]
  · change (onePointTuple e p hp t) (i.succ.succAbove k.succ) = e (t (i.succAbove k))
    rw [Fin.succ_succAbove_succ]
    rfl

private theorem new_pairWitness {r : ℕ} {V W : Type*}
    (hr : 2 ≤ r) (L : Hyper r V) (E : Hyper (r + 1) W)
    (e : V ↪ W) (p : W) (hp : p ∉ Set.range e)
    (hroot : ∀ t : Fin r ↪ V, E.orient (onePointTuple e p hp t) = L.orient t)
    (hcover : ∀ v : V, ∃ f : Fin (r + 1) ↪ V,
      v ∈ Set.range f ∧ localIndex L f = 0)
    (order : LinearOrder W) (v : V) : PairWitness E order p (e v) := by
  classical
  let := order
  let oldOrder : LinearOrder V := LinearOrder.lift' e e.injective
  let := oldOrder
  obtain ⟨f, hv, hzero⟩ := hcover v
  have hvmem : v ∈ tupleVertices f := (tupleVertices_mem_range f v).mpr hv
  obtain ⟨g, hg, hgv, hmono⟩ := packet_first f v hvmem
  have hgzero : localIndex L g = 0 := by
    rw [Antichain.localIndex_eq_of_tupleVertices_eq L g f hg]
    exact hzero
  obtain ⟨b, hb⟩ := (localIndex_zero_iff_normalized_constant L g).mp hgzero
  let i : Fin (r + 1) := ⟨1, by omega⟩
  let j : Fin (r + 1) := ⟨2, by omega⟩
  have hdiff : L.orient (facet g i) ≠ L.orient (facet g j) := by
    have hi := hb i
    have hj := hb j
    have hi' : (!L.orient (facet g i)) = b := by simpa [normalizedFacet, i] using hi
    have hj' : L.orient (facet g j) = b := by simpa [normalizedFacet, j] using hj
    intro h
    rw [h, hj'] at hi'
    cases b <;> simp_all
  let G := onePointTuple e p hp g
  have hG0 : G 0 = p := rfl
  have hG1 : G 1 = e v := by
    change e (g 0) = e v
    exact congrArg e hgv
  have hGmono : ∀ a c : Fin (r + 2), 2 ≤ a.val → a < c → G a < G c := by
    intro a c ha hac
    obtain ⟨a', rfl⟩ : ∃ a' : Fin (r + 1), a = a'.succ :=
      ⟨⟨a.val - 1, by omega⟩, Fin.ext (by simp; omega)⟩
    obtain ⟨c', rfl⟩ : ∃ c' : Fin (r + 1), c = c'.succ :=
      ⟨⟨c.val - 1, by omega⟩, Fin.ext (by simp; omega)⟩
    apply hmono a' c'
    · change 2 ≤ a'.val + 1 at ha
      omega
    · change a'.val + 1 < c'.val + 1 at hac
      omega
  refine ⟨facet G i.succ, facet G j.succ, ?_, ?_, ?_⟩
  · exact pairFirstTuple_facet_isPairLink G p (e v) hG0 hG1 hGmono _ (by simp [i])
  · exact pairFirstTuple_facet_isPairLink G p (e v) hG0 hG1 hGmono _ (by simp [j])
  · change E.orient (facet (onePointTuple e p hp g) i.succ) ≠
      E.orient (facet (onePointTuple e p hp g) j.succ)
    rw [facet_onePointTuple_succ, facet_onePointTuple_succ, hroot, hroot]
    exact hdiff

/-- A complete one-point gluing with a homogeneous covering link remains
pair-cancelling for every auxiliary order. -/
theorem pairCancelling_of_onePoint_link {r m : ℕ}
    (A : Hyper (r + 1) (Fin m)) (L : Hyper r (Fin m))
    (E : Hyper (r + 1) (Fin (m + 1)))
    (hA : PairCancelling A)
    (hold : Preserves A E (Fin.castSuccEmb (n := m)))
    (hp : Fin.last m ∉ Set.range (Fin.castSuccEmb (n := m)))
    (hroot : ∀ t : Fin r ↪ Fin m,
      E.orient (onePointTuple (Fin.castSuccEmb (n := m)) (Fin.last m) hp t) = L.orient t)
    (hcover : ∀ v : Fin m, ∃ f : Fin (r + 1) ↪ Fin m,
      v ∈ tupleVertices f ∧ localIndex L f = 0) : PairCancelling E := by
  have hr : 2 ≤ r := by have := hA.1; omega
  refine ⟨hA.1, ?_, ?_⟩
  · have hc := hA.2.1
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hc ⊢
    omega
  · intro order u v
    have hc : ∀ w : Fin m, ∃ f : Fin (r + 1) ↪ Fin m,
        w ∈ Set.range f ∧ localIndex L f = 0 := by
      intro w
      obtain ⟨f, hw, hz⟩ := hcover w
      exact ⟨f, (tupleVertices_mem_range f w).mp hw, hz⟩
    refine Fin.lastCases ?_ (fun a => ?_) u
    · refine Fin.lastCases ?_ (fun b => ?_) v
      · intro huv
        exact (huv rfl).elim
      · intro _
        exact new_pairWitness hr L E (Fin.castSuccEmb (n := m)) (Fin.last m) hp hroot hc order b
    · refine Fin.lastCases ?_ (fun b => ?_) v
      · intro _
        exact pairWitness_symm (by omega) E order
          (new_pairWitness hr L E (Fin.castSuccEmb (n := m)) (Fin.last m) hp hroot hc order a)
      · intro huv
        apply old_pairWitness A E (Fin.castSuccEmb (n := m)) hA hold order a b
        exact fun hab => huv (congrArg Fin.castSucc hab)

/-- Extend a pair-cancelling structure by exactly one vertex while retaining
all old orientations and realizing a homogeneous covering link at the new root. -/
theorem exists_pairCancelling_extension {r m : ℕ} (_hr : 2 ≤ r)
    (A : Hyper (r + 1) (Fin m)) (hA : PairCancelling A)
    (L : Hyper r (Fin m))
    (hL : ∀ v : Fin m, ∃ f : Fin (r + 1) ↪ Fin m,
      v ∈ tupleVertices f ∧ localIndex L f = 0) :
    ∃ E : Hyper (r + 1) (Fin (m + 1)),
      Preserves A E (Fin.castSuccEmb (n := m)) ∧ PairCancelling E := by
  obtain ⟨E, hold, hroot⟩ := exists_onePoint_glue A L
  exact ⟨E, hold, pairCancelling_of_onePoint_link A L E hA hold
    (last_not_mem_castSuccRange m) hroot hL⟩

end Hypertournaments.StrictConstraint
