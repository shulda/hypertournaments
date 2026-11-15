import Hypertournaments.EvenPotential
import Hypertournaments.CanonicalPacket
import Hypertournaments.CanonicalOrientationRecovery
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Fintype.EquivFin
import Lean.Elab.Tactic.Omega

/-!
# Relative gauge alignment of intrinsic potentials

A symmetric scalar coboundary shifts an alternating potential without changing
its next coboundary. Gauges extend by zero along arbitrary vertex embeddings.
The relative extension theorem includes an empty finite base in positive degree.
-/

namespace Hypertournaments

universe u v

/-- Exactness in positive degree does not require an inhabited carrier. -/
theorem coboundary_equal_on_positive_degree_implies_gauge
    {V : Type u} [DecidableEq V] (r : ℕ) (hr : 0 < r)
    (x h : Finset V → ZMod 2)
    (heq : ∀ Q : Finset V, Q.card = r + 1 →
      Hypertournaments.coboundary x Q = Hypertournaments.coboundary h Q) :
    ∃ z : Finset V → ZMod 2, ∀ Q : Finset V, Q.card = r →
      x Q = h Q + Hypertournaments.coboundary z Q := by
  classical
  by_cases hV : Nonempty V
  · exact coboundary_equal_on_degree_implies_gauge (Classical.choice hV) r x h heq
  · refine ⟨fun _ => 0, ?_⟩
    intro Q hQ
    have hne : Q.Nonempty := Finset.card_pos.mp (hQ ▸ hr)
    obtain ⟨a, _⟩ := hne
    exact (hV ⟨a⟩).elim

/-- Extend a scalar cochain by zero away from the image of an injection. -/
noncomputable def extendGauge {A : Type u} {C : Type v}
    (g : A ↪ C) (z : Finset A → ZMod 2) (Q : Finset C) : ZMod 2 := by
  classical
  exact if ∀ x ∈ Q, x ∈ Set.range g then z (Q.preimage g g.injective.injOn) else 0

@[simp] theorem extendGauge_map {A : Type u} {C : Type v}
    (g : A ↪ C) (z : Finset A → ZMod 2) (Q : Finset A) :
    extendGauge g z (Q.map g) = z Q := by
  classical
  have hinside : ∀ x ∈ Q.map g, x ∈ Set.range g := by
    intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
    exact ⟨a, rfl⟩
  simp only [extendGauge, ite_eq_left hinside, Finset.preimage_map]

theorem extendGauge_eq_zero_of_outside {A : Type u} {C : Type v}
    (g : A ↪ C) (z : Finset A → ZMod 2) (Q : Finset C)
    (h : ∃ x ∈ Q, x ∉ Set.range g) : extendGauge g z Q = 0 := by
  classical
  have hnot : ¬ ∀ x ∈ Q, x ∈ Set.range g := by
    obtain ⟨x, hx, hn⟩ := h
    exact fun ha => hn (ha x hx)
  simp only [extendGauge, ite_eq_right hnot]

/-- Extension commutes with coboundary when restricted back to the source. -/
theorem coboundary_extendGauge_map {A : Type u} {C : Type v}
    [DecidableEq A] [DecidableEq C]
    (g : A ↪ C) (z : Finset A → ZMod 2) (Q : Finset A) :
    Hypertournaments.coboundary (extendGauge g z) (Q.map g) =
      Hypertournaments.coboundary z Q := by
  classical
  unfold Hypertournaments.coboundary
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.map_erase g Q x, extendGauge_map]

/-- Tuple supports commute with every injection, independently of orders. -/
theorem tupleVertices_trans_map {r : ℕ} {A : Type u} {C : Type v}
    [DecidableEq A] [DecidableEq C] (f : Fin r ↪ A) (g : A ↪ C) :
    tupleVertices (f.trans g) = (tupleVertices f).map g := by
  simp only [tupleVertices, Finset.map_eq_image, Finset.image_image]
  rfl

/-- The tuple coboundary of a symmetric cochain is its scalar coboundary. -/
theorem tupleCoboundary_symmetric {r : ℕ} {V : Type u} [DecidableEq V]
    (z : Finset V → ZMod 2) (f : Fin (r + 1) ↪ V) :
    tupleCoboundary (fun t => z (tupleVertices t)) f =
      Hypertournaments.coboundary z (tupleVertices f) := by
  classical
  unfold tupleCoboundary Hypertournaments.coboundary
  change (∑ i : Fin (r + 1), z (tupleVertices (facet f i))) =
    ∑ x ∈ Finset.univ.image f, z ((tupleVertices f).erase x)
  rw [Finset.sum_image]
  · exact Finset.sum_congr rfl (fun i _ => congrArg z (tupleVertices_facet_eq_erase f i))
  · intro i _ j _ h
    exact f.injective h

/-- Shift an intrinsic orientation by a symmetric scalar function on supports. -/
def Hyper.cochainShift {r : ℕ} {V : Type u} [DecidableEq V]
    (φ : Hyper r V) (z : Finset V → ZMod 2) : Hyper r V where
  orient f := p3ZMod2ToBool (p1BitToZMod (φ.orient f) + z (tupleVertices f))
  swap_flip f i j hij := by
    apply p1BitToZMod_injective
    rw [p3BitToZMod_roundtrip, p1BitToZMod_not, p3BitToZMod_roundtrip,
      φ.swap_flip f i j hij, p1BitToZMod_not, tupleVertices_swap]
    exact add_right_comm _ _ _

@[simp] theorem Hyper.cochainShift_orient_bit {r : ℕ} {V : Type u} [DecidableEq V]
    (φ : Hyper r V) (z : Finset V → ZMod 2) (f : Fin r ↪ V) :
    p1BitToZMod ((φ.cochainShift z).orient f) =
      p1BitToZMod (φ.orient f) + z (tupleVertices f) :=
  p3BitToZMod_roundtrip _

/-- An exact symmetric shift preserves the actual raw tuple coboundary. -/
theorem Hyper.cochainShift_coboundary {r : ℕ} {V : Type u} [DecidableEq V]
    (φ : Hyper r V) (z : Finset V → ZMod 2) (f : Fin (r + 1) ↪ V) :
    tupleCoboundary (fun t => p1BitToZMod
      ((φ.cochainShift (Hypertournaments.coboundary z)).orient t)) f =
      tupleCoboundary (fun t => p1BitToZMod (φ.orient t)) f := by
  simp only [Hyper.cochainShift_orient_bit]
  rw [tupleCoboundary_add, tupleCoboundary_symmetric, coboundary_coboundary_zero, add_zero]

theorem IsPotential.cochainShift {r : ℕ} {V : Type u} [DecidableEq V]
    {A : Hyper (r + 1) V} {φ : Hyper r V} (hφ : IsPotential A φ)
    (z : Finset V → ZMod 2) : IsPotential A (φ.cochainShift (Hypertournaments.coboundary z)) := by
  intro f
  rw [Hyper.cochainShift_coboundary]
  exact hφ f

/-- Empty-base-safe canonical gauge alignment in every positive degree. -/
theorem IsPotential.canonical_gauge_pos {r a : ℕ}
    {A : Hyper (r + 1) (Fin a)} {φ ψ : Hyper r (Fin a)}
    (hφ : IsPotential A φ) (hψ : IsPotential A ψ) (hr : 0 < r) :
    ∃ z : Finset (Fin a) → ZMod 2, ∀ Q : Finset (Fin a), Q.card = r →
      p1BitToZMod (φ.canonicalSignTable Q) =
        p1BitToZMod (ψ.canonicalSignTable Q) + Hypertournaments.coboundary z Q := by
  classical
  by_cases h : Nonempty (Fin a)
  · exact hφ.canonical_gauge hψ (Classical.choice h)
  · refine ⟨fun _ => 0, ?_⟩
    intro Q hQ
    have hne : Q.Nonempty := Finset.card_pos.mp (hQ ▸ hr)
    obtain ⟨x, _⟩ := hne
    exact (h ⟨x⟩).elim

/-- Canonical exactness recovers the gauge equation on every ordered tuple. -/
theorem IsPotential.intrinsic_gauge_fin {r a : ℕ}
    {A : Hyper (r + 1) (Fin a)} {φ ψ : Hyper r (Fin a)}
    (hφ : IsPotential A φ) (hψ : IsPotential A ψ) (hr : 0 < r) :
    ∃ z : Finset (Fin a) → ZMod 2, ∀ t : Fin r ↪ Fin a,
      p1BitToZMod (φ.orient t) = p1BitToZMod (ψ.orient t) +
        Hypertournaments.coboundary z (tupleVertices t) := by
  classical
  obtain ⟨z, hz⟩ := hφ.canonical_gauge_pos hψ hr
  have heq : ∀ t : Fin r ↪ Fin a,
      φ.orient t = (ψ.cochainShift (Hypertournaments.coboundary z)).orient t := by
    apply orientations_equal_of_canonical
    intro Q hQ
    apply p1BitToZMod_injective
    rw [Hyper.cochainShift_orient_bit]
    have hvertices : tupleVertices (Q.orderEmbOfFin hQ).toEmbedding = Q :=
      Finset.image_orderEmbOfFin_univ Q hQ
    rw [hvertices]
    have hh := hz Q hQ
    rw [Hyper.canonicalSignTable_at φ Q hQ, Hyper.canonicalSignTable_at ψ Q hQ] at hh
    exact hh
  refine ⟨z, ?_⟩
  intro t
  rw [heq t, Hyper.cochainShift_orient_bit]

/-- Two intrinsic potentials of the same orientation differ by an exact
symmetric cochain on all actual tuples, without choosing a carrier order. -/
theorem IsPotential.intrinsic_gauge {r : ℕ} {V : Type u} [Finite V] [DecidableEq V]
    {A : Hyper (r + 1) V} {φ ψ : Hyper r V}
    (hφ : IsPotential A φ) (hψ : IsPotential A ψ) (hr : 0 < r) :
    ∃ z : Finset V → ZMod 2, ∀ t : Fin r ↪ V,
      p1BitToZMod (φ.orient t) = p1BitToZMod (ψ.orient t) +
        Hypertournaments.coboundary z (tupleVertices t) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let s := (Fintype.equivFin V).symm
  obtain ⟨z, hz⟩ := (hφ.pullback s.toEmbedding).intrinsic_gauge_fin
    (hψ.pullback s.toEmbedding) hr
  refine ⟨extendGauge s.toEmbedding z, ?_⟩
  intro t
  let t' := t.trans s.symm.toEmbedding
  have ht : t'.trans s.toEmbedding = t := by
    ext i
    simp [t']
  have hvertices : tupleVertices t = (tupleVertices t').map s.toEmbedding := by
    rw [← ht, tupleVertices_trans_map]
  have hh := hz t'
  change p1BitToZMod (φ.orient (t'.trans s.toEmbedding)) =
    p1BitToZMod (ψ.orient (t'.trans s.toEmbedding)) +
      Hypertournaments.coboundary z (tupleVertices t') at hh
  rw [ht] at hh
  rw [hvertices, coboundary_extendGauge_map]
  exact hh

/-- Relative potential extension from a canonically indexed finite base. -/
theorem IsPotential.exists_aligned_fin {r a : ℕ} {C : Type v}
    {CC : Hyper (r + 1) C} {ψ : Hyper r C} (hψ : IsPotential CC ψ)
    (φA : Hyper r (Fin a)) (g : Fin a ↪ C)
    (hφA : IsPotential (CC.pullback g) φA) (hr : 0 < r) :
    ∃ ψ' : Hyper r C, IsPotential CC ψ' ∧ Preserves φA ψ' g := by
  classical
  obtain ⟨z, hz⟩ := hφA.canonical_gauge_pos (hψ.pullback g) hr
  let extended := extendGauge g z
  let ψ' := ψ.cochainShift (Hypertournaments.coboundary extended)
  refine ⟨ψ', hψ.cochainShift extended, ?_⟩
  apply preserves_of_canonical φA ψ' g
  intro Q hQ
  apply p1BitToZMod_injective
  have hvertices : tupleVertices (Q.orderEmbOfFin hQ).toEmbedding = Q :=
    Finset.image_orderEmbOfFin_univ Q hQ
  rw [Hyper.cochainShift_orient_bit, tupleVertices_trans_map,
    hvertices, coboundary_extendGauge_map]
  have hh := hz Q hQ
  rw [Hyper.canonicalSignTable_at φA Q hQ,
    Hyper.canonicalSignTable_at (ψ.pullback g) Q hQ] at hh
  exact hh.symm

/-- Any prescribed potential on a finite base extends to a potential of the
whole orientation, by aligning an existing potential through an exact gauge. -/
theorem IsPotential.exists_aligned {r : ℕ} {A : Type u} {C : Type v} [Finite A]
    {CC : Hyper (r + 1) C} {ψ : Hyper r C} (hψ : IsPotential CC ψ)
    (φA : Hyper r A) (g : A ↪ C)
    (hφA : IsPotential (CC.pullback g) φA) (hr : 0 < r) :
    ∃ ψ' : Hyper r C, IsPotential CC ψ' ∧ Preserves φA ψ' g := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let s := (Fintype.equivFin A).symm
  let g' := s.toEmbedding.trans g
  obtain ⟨ψ', hψ', hPres⟩ := hψ.exists_aligned_fin (φA.pullback s.toEmbedding) g'
    (hφA.pullback s.toEmbedding) hr
  refine ⟨ψ', hψ', ?_⟩
  intro t
  let t' := t.trans s.symm.toEmbedding
  have hh := hPres t'
  have hleft : t'.trans g' = t.trans g := by
    ext i
    simp [t', g']
  have hright : t'.trans s.toEmbedding = t := by
    ext i
    simp [t']
  change ψ'.orient (t'.trans g') = φA.orient (t'.trans s.toEmbedding) at hh
  rw [hleft, hright] at hh
  exact hh

end Hypertournaments
