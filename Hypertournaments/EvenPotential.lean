import Hypertournaments.HyperCoboundary
import Hypertournaments.CoboundaryGauge

/-!
# Potentials of even hypertournaments

An intrinsic potential is an alternating orientation in the preceding arity,
whose unsigned coboundary is the actual orientation function. The finite
existence proof uses the elementary simplex contraction on canonical sign
tables and then recovers all ordered tuples by alternation.
-/

namespace Hypertournaments

universe u v

/-- A potential recovers the actual orientation on every injective ordered
tuple, without changing the normalization of its facets. -/
def IsPotential {r : ℕ} {V : Type u}
    (A : Hyper (r + 1) V) (φ : Hyper r V) : Prop :=
  ∀ f : Fin (r + 1) ↪ V,
    tupleCoboundary (fun t => p1BitToZMod (φ.orient t)) f =
      p1BitToZMod (A.orient f)

/-- Restricting both orientations along the same vertex injection preserves
the potential equation. -/
theorem IsPotential.pullback {r : ℕ} {V : Type u} {W : Type v}
    {A : Hyper (r + 1) W} {φ : Hyper r W} (h : IsPotential A φ)
    (e : V ↪ W) : IsPotential (A.pullback e) (φ.pullback e) := by
  intro f
  exact h (f.trans e)

/-- A potential on any equivalent vertex presentation transports back to
the original carrier. -/
theorem IsPotential.of_equiv_pullback {r : ℕ} {V : Type u} {W : Type v}
    {A : Hyper (r + 1) V} (e : V ≃ W) {ψ : Hyper r W}
    (h : IsPotential (A.pullback e.symm.toEmbedding) ψ) :
    IsPotential A (ψ.pullback e.toEmbedding) := by
  intro f
  have hf := h (f.trans e.toEmbedding)
  have he : (f.trans e.toEmbedding).trans e.symm.toEmbedding = f := by
    ext i
    exact e.symm_apply_apply (f i)
  change tupleCoboundary (fun t => p1BitToZMod
      ((ψ.pullback e.toEmbedding).orient t)) f =
    p1BitToZMod (A.orient ((f.trans e.toEmbedding).trans e.symm.toEmbedding)) at hf
  simpa only [he] using hf

/-- The intrinsic potential equation forces closedness, without any arity,
finiteness, or nonemptiness assumption. -/
theorem IsPotential.isEven {r : ℕ} {V : Type u}
    {A : Hyper (r + 1) V} {φ : Hyper r V} (h : IsPotential A φ) : A.IsEven := by
  intro f
  have heq : tupleCoboundary (fun t => p1BitToZMod (A.orient t)) f =
      tupleCoboundary (tupleCoboundary (fun t => p1BitToZMod (φ.orient t))) f := by
    apply Finset.sum_congr rfl
    intro i _
    exact (h (facet f i)).symm
  rw [heq, tupleCoboundary_tupleCoboundary_zero]

/-- An intrinsic potential determines its upper orientation uniquely. -/
theorem IsPotential.unique {r : ℕ} {V : Type u}
    {A B : Hyper (r + 1) V} {φ : Hyper r V}
    (hA : IsPotential A φ) (hB : IsPotential B φ) : A = B := by
  apply Hyper.ext
  intro f
  exact p1BitToZMod_injective ((hA f).symm.trans (hB f))

/-- An embedding preserving chosen potentials automatically preserves the
upper orientations. This uses the actual tuple equation on both carriers. -/
theorem IsPotential.preserves {r : ℕ} {V : Type u} {W : Type v}
    {A : Hyper (r + 1) V} {B : Hyper (r + 1) W}
    {φ : Hyper r V} {ψ : Hyper r W}
    (hA : IsPotential A φ) (hB : IsPotential B ψ)
    {e : V ↪ W} (h : Preserves φ ψ e) : Preserves A B e := by
  intro f
  apply p1BitToZMod_injective
  rw [← hB (f.trans e), ← hA f]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg p1BitToZMod (h (facet f i))

/-- Canonical sign-table coboundaries compute the raw intrinsic tuple
coboundary on increasing packets. -/
theorem Hyper.canonical_coboundary_eq_tuple
    {r a : ℕ} (A : Hyper r (Fin a)) (f : Fin (r + 1) ↪o Fin a) :
    Hypertournaments.coboundary (fun Q => p1BitToZMod (A.canonicalSignTable Q))
      (tupleVertices f.toEmbedding) =
      tupleCoboundary (fun t => p1BitToZMod (A.orient t)) f.toEmbedding := by
  rw [A.p1CanonicalRawFacetSum f, p1BoolPacketPositiveCount_toZMod]
  rfl

/-- Every field-valued canonical sign table is realized by an intrinsic
alternating orientation, in any arity. -/
theorem fromOrderedSigns_canonical_bit
    {r a : ℕ} (z : Finset (Fin a) → ZMod 2)
    (Q : Finset (Fin a)) (hQ : Q.card = r) :
    p1BitToZMod ((Hyper.fromOrderedSigns (fun S => p3ZMod2ToBool (z S)) :
      Hyper r (Fin a)).canonicalSignTable Q) = z Q := by
  rw [Hyper.canonicalSignTable_at _ Q hQ]
  rw [fromOrderedSigns_orient_strictMono _ _ (Q.orderEmbOfFin hQ).strictMono]
  have hv : tupleVertices (Q.orderEmbOfFin hQ).toEmbedding = Q :=
    Finset.image_orderEmbOfFin_univ Q hQ
  rw [hv, p3BitToZMod_roundtrip]

/-- Closedness of actual ordered-tuple orientations implies a canonical
scalar potential, by the explicit simplex contraction at any vertex. -/
theorem Hyper.canonical_potential_of_closed
    {r a : ℕ} (A : Hyper (r + 1) (Fin a)) (root : Fin a)
    (hclosed : ∀ f : Fin ((r + 1) + 1) ↪ Fin a,
      tupleCoboundary (fun t => p1BitToZMod (A.orient t)) f = 0) :
    ∃ z : Finset (Fin a) → ZMod 2,
      ∀ Q : Finset (Fin a), Q.card = r + 1 →
        Hypertournaments.coboundary z Q = p1BitToZMod (A.canonicalSignTable Q) := by
  let e : Finset (Fin a) → ZMod 2 :=
    fun Q => p1BitToZMod (A.canonicalSignTable Q)
  have hc (Q : Finset (Fin a)) (hQ : Q.card = (r + 1) + 1) :
      Hypertournaments.coboundary e Q = 0 := by
    let f : Fin ((r + 1) + 1) ↪o Fin a := Q.orderEmbOfFin hQ
    have hv : tupleVertices f.toEmbedding = Q :=
      Finset.image_orderEmbOfFin_univ Q hQ
    have h := (A.canonical_coboundary_eq_tuple f).trans (hclosed f.toEmbedding)
    simpa only [hv] using h
  exact ⟨contractAt root e, cocycle_exact_at_card root (r + 1) e hc⟩

/-- Realizing a canonical scalar cochain preserves its coboundary in the
next degree. -/
theorem fromOrderedSigns_canonical_coboundary
    {r a : ℕ} (z : Finset (Fin a) → ZMod 2)
    (Q : Finset (Fin a)) (hQ : Q.card = r + 1) :
    coboundary (fun S => p1BitToZMod
      ((Hyper.fromOrderedSigns (fun T => p3ZMod2ToBool (z T)) :
        Hyper r (Fin a)).canonicalSignTable S)) Q = coboundary z Q := by
  apply Finset.sum_congr rfl
  intro x hx
  have hS : (Q.erase x).card = r := by
    rw [Finset.card_erase_of_mem hx, hQ]
    omega
  exact fromOrderedSigns_canonical_bit z (Q.erase x) hS

/-- Two intrinsic potentials of one orientation differ by a scalar
coboundary on canonical tuples. The anchor is explicit. -/
theorem IsPotential.canonical_gauge
    {r a : ℕ} {A : Hyper (r + 1) (Fin a)} {φ ψ : Hyper r (Fin a)}
    (hφ : IsPotential A φ) (hψ : IsPotential A ψ) (root : Fin a) :
    ∃ u : Finset (Fin a) → ZMod 2,
      ∀ Q : Finset (Fin a), Q.card = r →
        p1BitToZMod (φ.canonicalSignTable Q) =
          p1BitToZMod (ψ.canonicalSignTable Q) + coboundary u Q := by
  apply coboundary_equal_on_degree_implies_gauge root r
  intro Q hQ
  let f : Fin (r + 1) ↪o Fin a := Q.orderEmbOfFin hQ
  have hv : tupleVertices f.toEmbedding = Q :=
    Finset.image_orderEmbOfFin_univ Q hQ
  rw [← hv, φ.canonical_coboundary_eq_tuple f, ψ.canonical_coboundary_eq_tuple f]
  exact (hφ f.toEmbedding).trans (hψ f.toEmbedding).symm

/-- The intrinsic coboundary comes with its defining potential. -/
theorem Hyper.coboundary_isPotential {r : ℕ} {V : Type u}
    (φ : Hyper r V) (hr : Even r) : IsPotential (φ.coboundary hr) φ := by
  intro f
  exact (φ.coboundary_orient hr f).symm

/-- The raw potential equation is equivalent to equality of the intrinsic
coboundary and the upper hypertournament. -/
theorem isPotential_iff_coboundary_eq {r : ℕ} {V : Type u}
    (A : Hyper (r + 1) V) (φ : Hyper r V) (hr : Even r) :
    IsPotential A φ ↔ φ.coboundary hr = A := by
  constructor
  · intro h
    exact (φ.coboundary_isPotential hr).unique h
  · rintro rfl
    exact φ.coboundary_isPotential hr

/-- A scalar potential on canonical subsets realizes an intrinsic potential
on all ordered tuples, because both upper orientations alternate. -/
theorem Hyper.isPotential_from_canonical_cochain
    {r a : ℕ} (hr : Even r) (A : Hyper (r + 1) (Fin a))
    (z : Finset (Fin a) → ZMod 2)
    (hz : ∀ Q : Finset (Fin a), Q.card = r + 1 →
      Hypertournaments.coboundary z Q = p1BitToZMod (A.canonicalSignTable Q)) :
    IsPotential A (Hyper.fromOrderedSigns (fun Q => p3ZMod2ToBool (z Q))) := by
  let φ : Hyper r (Fin a) :=
    Hyper.fromOrderedSigns (fun Q => p3ZMod2ToBool (z Q))
  have hc : ∀ (Q : Finset (Fin a)) (hQ : Q.card = r + 1),
      (φ.coboundary hr).orient (Q.orderEmbOfFin hQ).toEmbedding =
        A.orient (Q.orderEmbOfFin hQ).toEmbedding := by
    intro Q hQ
    let f : Fin (r + 1) ↪o Fin a := Q.orderEmbOfFin hQ
    have hv : tupleVertices f.toEmbedding = Q :=
      Finset.image_orderEmbOfFin_univ Q hQ
    apply p1BitToZMod_injective
    rw [φ.coboundary_orient hr, ← φ.canonical_coboundary_eq_tuple f, hv]
    rw [fromOrderedSigns_canonical_coboundary z Q hQ, hz Q hQ,
      A.canonicalSignTable_at Q hQ]
  have hall := orientations_equal_of_canonical (φ.coboundary hr) A hc
  intro f
  exact (φ.coboundary_orient hr f).symm.trans (congrArg p1BitToZMod (hall f))

/-- Every even upper orientation on a finite ordinal has an intrinsic
potential in the preceding even arity. The empty carrier is included. -/
theorem Hyper.exists_potential_fin {r a : ℕ} (hr : Even r)
    (A : Hyper (r + 1) (Fin a)) (hA : A.IsEven) :
    ∃ φ : Hyper r (Fin a), IsPotential A φ := by
  cases a with
  | zero =>
    refine ⟨Hyper.fromOrderedSigns (fun _ => false), ?_⟩
    intro f
    exact Fin.elim0 (f 0)
  | succ a =>
    obtain ⟨z, hz⟩ := A.canonical_potential_of_closed (0 : Fin (a + 1)) hA
    exact ⟨_, A.isPotential_from_canonical_cochain hr z hz⟩

/-- Every finite intrinsic even hypertournament has a genuine intrinsic
potential, uniformly in the finite carrier and including the empty case. -/
theorem Hyper.exists_potential {r : ℕ} {V : Type u} [Finite V]
    (hr : Even r) (A : Hyper (r + 1) V) (hA : A.IsEven) :
    ∃ φ : Hyper r V, IsPotential A φ := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  obtain ⟨ψ, hψ⟩ := (A.pullback e.symm.toEmbedding).exists_potential_fin hr
    (hA.pullback e.symm.toEmbedding)
  exact ⟨ψ.pullback e.toEmbedding, hψ.of_equiv_pullback e⟩

/-- On finite carriers, evenness is exactly the existence of an intrinsic
potential whenever the preceding arity is even. -/
theorem Hyper.isEven_iff_exists_potential {r : ℕ} {V : Type u} [Finite V]
    (hr : Even r) (A : Hyper (r + 1) V) :
    A.IsEven ↔ ∃ φ : Hyper r V, IsPotential A φ := by
  constructor
  · exact A.exists_potential hr
  · rintro ⟨φ, hφ⟩
    exact hφ.isEven

end Hypertournaments
