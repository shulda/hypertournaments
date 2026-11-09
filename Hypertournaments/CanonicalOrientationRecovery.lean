import Hypertournaments.FinitePresentation
import Hypertournaments.TwoPadSlice

/-!
# Ordered certificates for intrinsic source-orientation recovery

For any n-ary hypertournaments on a finite ordered vertex set, it
suffices to compare their orientations on increasing n-tuples. Every
injective tuple is a reordering of the unique increasing enumeration
of its image. The alternating orientation law transports equality
through the corresponding arbitrary permutation.

This result makes the even/odd two-coordinate suspension construction
substantially easier to certify: its source-recovery identity need
only be checked on canonical increasing old subsets, rather than all
ordered injective tuples.

It is not an admissibility or AP claim; it is a pure finite-orientation
certificate bridge, independent of fixed arity.
-/

namespace Hypertournaments

/-- Two arbitrary intrinsic n-hyperorientations on Fin k agree on
all ordered injective n-tuples as soon as they agree on every
canonical increasing n-element subset. -/
theorem orientations_equal_of_canonical
    {n k : ℕ} (A B : Hyper n (Fin k))
    (h : ∀ (Q : Finset (Fin k)) (hQ : Q.card = n),
      A.orient (Q.orderEmbOfFin hQ).toEmbedding =
      B.orient (Q.orderEmbOfFin hQ).toEmbedding) :
    ∀ f : Fin n ↪ Fin k, A.orient f = B.orient f := by
  intro f
  let Q : Finset (Fin k) := tupleVertices f
  have hQ : Q.card = n := by
    dsimp [Q, tupleVertices]
    rw [Finset.card_image_of_injective _ f.injective]
    simp
  let g : Fin n ↪o Fin k := Q.orderEmbOfFin hQ
  let τ : Equiv.Perm (Fin n) := Tuple.sort (f : Fin n → Fin k)
  have hmono : Monotone ((f : Fin n → Fin k) ∘ τ) :=
    Tuple.monotone_sort (f : Fin n → Fin k)
  have hinj : Function.Injective ((f : Fin n → Fin k) ∘ τ) :=
    f.injective.comp τ.injective
  have hsorted : (f : Fin n → Fin k) ∘ τ = (g : Fin n → Fin k) := by
    exact Finset.orderEmbOfFin_unique hQ (by
      intro i
      change f (τ i) ∈ Q
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _))
      (hmono.strictMono_of_injective hinj)
  have hreorder : τ.symm.toEmbedding.trans g.toEmbedding = f := by
    ext x
    have hx := congrFun hsorted (τ.symm x)
    exact congrArg Fin.val (by simpa [Function.comp_apply] using hx.symm)
  have heq : A.orient g.toEmbedding = B.orient g.toEmbedding := h Q hQ
  calc
    A.orient f =
        A.orient (τ.symm.toEmbedding.trans g.toEmbedding) := by rw [hreorder]
    _ = (if Equiv.Perm.sign τ.symm = (1 : ℤˣ) then
          A.orient g.toEmbedding else !(A.orient g.toEmbedding)) :=
      A.orient_perm g.toEmbedding τ.symm
    _ = (if Equiv.Perm.sign τ.symm = (1 : ℤˣ) then
          B.orient g.toEmbedding else !(B.orient g.toEmbedding)) := by
      rw [heq]
    _ = B.orient (τ.symm.toEmbedding.trans g.toEmbedding) :=
      (B.orient_perm g.toEmbedding τ.symm).symm
    _ = B.orient f := by rw [hreorder]

/-- Source orientation recovery from a lifted n+2 orientation can be
checked on increasing n-subsets only, even though its conclusion
covers all arbitrary ordered injective n-tuples. -/
theorem twoPad_source_recovery_of_canonical
    {n k : ℕ} {V : Type*}
    (L : Hyper n (Fin k))
    (D : Hyper (n + 2) V)
    (g : Fin k ↪ V) (p q : V)
    (hp : p ∉ Set.range g) (hq : q ∉ Set.range g)
    (hpq : p ≠ q)
    (h : ∀ (Q : Finset (Fin k)) (hQ : Q.card = n),
      D.orient (twoPadSliceTuple g p q hp hq hpq
          (Q.orderEmbOfFin hQ).toEmbedding) =
        L.orient (Q.orderEmbOfFin hQ).toEmbedding) :
    ∀ t : Fin n ↪ Fin k,
      D.orient (twoPadSliceTuple g p q hp hq hpq t) = L.orient t := by
  have hc : ∀ Q : Finset (Fin k), ∀ hQ : Q.card = n,
      (D.twoPadSlice g p q hp hq hpq).orient
          (Q.orderEmbOfFin hQ).toEmbedding =
        L.orient (Q.orderEmbOfFin hQ).toEmbedding := h
  intro t
  exact orientations_equal_of_canonical
    (D.twoPadSlice g p q hp hq hpq) L hc t


/-- A vertex embedding preserves *all* oriented n-tuples as soon as
orientation preservation has been checked on the increasing n-tuples
of the finite source. No order-preservation is required of f. -/
theorem preserves_of_canonical
    {n k : ℕ} {V : Type*}
    (A : Hyper n (Fin k)) (B : Hyper n V)
    (f : Fin k ↪ V)
    (h : ∀ (Q : Finset (Fin k)) (hQ : Q.card = n),
      B.orient ((Q.orderEmbOfFin hQ).toEmbedding.trans f) =
        A.orient (Q.orderEmbOfFin hQ).toEmbedding) :
    Preserves A B f := by
  intro t
  exact orientations_equal_of_canonical
    (B.pullback f) A (fun Q hQ => h Q hQ) t

end Hypertournaments
