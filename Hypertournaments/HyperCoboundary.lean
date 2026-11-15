import Hypertournaments.TupleCoboundary
import Hypertournaments.GeneralAdjacentFacet
import Hypertournaments.OddToggleP3PotentialPresentation

/-!
# Intrinsic coboundaries of even-arity hypertournaments

The unsigned tuple coboundary changes by one under a transposition precisely
when the source arity is even. It therefore supplies an intrinsic hypertournament
in the next arity. No auxiliary vertex order enters the construction.
-/

namespace Hypertournaments

universe u v

theorem p1BitToZMod_injective : Function.Injective p1BitToZMod := by
  intro b c h
  cases b <;> cases c <;> simp_all [p1BitToZMod]

theorem p1BitToZMod_not (b : Bool) : p1BitToZMod (!b) = p1BitToZMod b + 1 := by
  cases b <;> decide

@[ext] theorem Hyper.ext {n : ℕ} {V : Type u} {A B : Hyper n V}
    (h : ∀ f, A.orient f = B.orient f) : A = B := by
  cases A with | mk ao aswap =>
    cases B with | mk bo bswap =>
      have hfun : ao = bo := funext h
      cases hfun
      rfl

/-- Evenness is the zero raw unsigned facet sum on every injective tuple. -/
def Hyper.IsEven {n : ℕ} {V : Type u} (A : Hyper n V) : Prop :=
  ∀ f : Fin (n + 1) ↪ V,
    tupleCoboundary (fun t => p1BitToZMod (A.orient t)) f = 0

theorem Hyper.IsEven.pullback {n : ℕ} {V : Type u} {W : Type v}
    {A : Hyper n W} (hA : A.IsEven) (e : V ↪ W) : (A.pullback e).IsEven := by
  intro f
  exact hA (f.trans e)


private def permutationParity {m : ℕ} (σ : Equiv.Perm (Fin m)) : ZMod 2 :=
  if σ.sign = 1 then 0 else 1

private theorem permutationParity_mul {m : ℕ} (σ τ : Equiv.Perm (Fin m)) :
    permutationParity (σ * τ) = permutationParity σ + permutationParity τ := by
  rcases Int.units_eq_one_or σ.sign with hs | hs <;>
    rcases Int.units_eq_one_or τ.sign with ht | ht <;>
    simp [permutationParity, Equiv.Perm.sign_mul, hs, ht, Units.ext_iff] <;> decide +kernel

private theorem even_cast_zmod_two {r : ℕ} (hr : Even r) : (r : ZMod 2) = 0 := by
  obtain ⟨k, hk⟩ := hr
  rw [hk, Nat.cast_add]
  simpa only [ZMod.neg_eq_self_mod_two] using add_neg_cancel (k : ZMod 2)

/-- Adjacent coordinate exchange changes the raw facet sum by the packet
length in F₂. This formula holds in every source arity. -/
theorem tupleCoboundary_orient_adjacent {r : ℕ} {V : Type u}
    (A : Hyper r V) (f : Fin (r + 1) ↪ V) (p : Fin r) :
    tupleCoboundary (fun t => p1BitToZMod (A.orient t))
      ((adjacentSwapCoord p).toEmbedding.trans f) =
    tupleCoboundary (fun t => p1BitToZMod (A.orient t)) f + (r + 1 : ℕ) := by
  let raw := tupleCoboundary (fun t => p1BitToZMod (A.orient t))
  let normal := fun g : Fin (r + 1) ↪ V =>
    ∑ i : Fin (r + 1), p1BitToZMod (normalizedFacet A g i)
  let K : ZMod 2 := ∑ i : Fin (r + 1), p1BitToZMod (decide (i.val % 2 = 1))
  have hnormal (g : Fin (r + 1) ↪ V) : normal g = raw g + K := by
    simp only [normal, raw, K, normalizedFacet, p1BitToZMod_xor,
      tupleCoboundary, Finset.sum_add_distrib]
  have hs : normal ((adjacentSwapCoord p).toEmbedding.trans f) = normal f + (r + 1 : ℕ) := by
    calc
      normal ((adjacentSwapCoord p).toEmbedding.trans f) =
          ∑ i : Fin (r + 1), (p1BitToZMod (normalizedFacet A f (adjacentSwapCoord p i)) + 1) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [normalizedFacet_adjacent_swap A f p i, p1BitToZMod_not]
      _ = (∑ i : Fin (r + 1), p1BitToZMod (normalizedFacet A f (adjacentSwapCoord p i))) +
          (r + 1 : ℕ) := by rw [Finset.sum_add_distrib]; simp
      _ = normal f + (r + 1 : ℕ) :=
        congrArg (fun x : ZMod 2 => x + (r + 1 : ℕ))
          (Equiv.sum_comp (adjacentSwapCoord p) (fun i => p1BitToZMod (normalizedFacet A f i)))
  have hh : raw ((adjacentSwapCoord p).toEmbedding.trans f) + K =
      (raw f + (r + 1 : ℕ)) + K := by
    rw [← hnormal, hs, hnormal]
    simp only [add_assoc, add_left_comm, add_comm]
  exact add_right_cancel hh

/-- In even source arity, the raw coboundary has the full permutation parity
law of an alternating orientation. Adjacent transpositions generate the group. -/
theorem tupleCoboundary_orient_perm {r : ℕ} {V : Type u}
    (A : Hyper r V) (hr : Even r) (f : Fin (r + 1) ↪ V)
    (σ : Equiv.Perm (Fin (r + 1))) :
    tupleCoboundary (fun t => p1BitToZMod (A.orient t)) (σ.toEmbedding.trans f) =
      tupleCoboundary (fun t => p1BitToZMod (A.orient t)) f +
        (if σ.sign = 1 then 0 else 1) := by
  let raw := tupleCoboundary (fun t => p1BitToZMod (A.orient t))
  have hcast : ((r + 1 : ℕ) : ZMod 2) = 1 := by
    simp only [Nat.cast_add, Nat.cast_one, even_cast_zmod_two hr, zero_add]
  let generators : Set (Equiv.Perm (Fin (r + 1))) :=
    Set.range (fun p : Fin r => adjacentSwapCoord p)
  have hgen : Submonoid.closure generators = ⊤ := Equiv.Perm.mclosure_swap_castSucc_succ r
  have hall : ∀ τ : Equiv.Perm (Fin (r + 1)), τ ∈ Submonoid.closure generators →
      ∀ g : Fin (r + 1) ↪ V, raw (τ.toEmbedding.trans g) = raw g + permutationParity τ := by
    intro τ hτ
    induction hτ using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      intro g
      have hne : p.castSucc ≠ p.succ := by
        intro he
        have hh := congrArg Fin.val he
        simp only [Fin.val_castSucc, Fin.val_succ] at hh
        omega
      have hp : permutationParity (adjacentSwapCoord p) = 1 := by
        simp [permutationParity, adjacentSwapCoord, Equiv.Perm.sign_swap hne, Units.ext_iff]
      change tupleCoboundary (fun t => p1BitToZMod (A.orient t)) _ = _
      rw [tupleCoboundary_orient_adjacent, hcast, hp]
    | one =>
      intro g
      have hg : ((1 : Equiv.Perm (Fin (r + 1))).toEmbedding.trans g) = g := by ext i; rfl
      rw [hg]
      simp [permutationParity]
    | mul x y hx hy ihx ihy =>
      intro g
      have hcomp : (x * y).toEmbedding.trans g = y.toEmbedding.trans (x.toEmbedding.trans g) := by
        ext i
        rfl
      rw [hcomp, ihy, ihx, permutationParity_mul]
      exact add_assoc _ _ _
  apply hall σ
  rw [hgen]
  trivial

private theorem zmodBit_add_one (x : ZMod 2) :
    p3ZMod2ToBool (x + 1) = !(p3ZMod2ToBool x) := by
  have h : ∀ x : ZMod 2, p3ZMod2ToBool (x + 1) = !(p3ZMod2ToBool x) := by decide +kernel
  exact h x

/-- The intrinsic coboundary of an even-arity hypertournament. -/
def Hyper.coboundary {r : ℕ} {V : Type u} (A : Hyper r V) (hr : Even r) : Hyper (r + 1) V where
  orient f := p3ZMod2ToBool (tupleCoboundary (fun t => p1BitToZMod (A.orient t)) f)
  swap_flip f i j hij := by
    have hsum := tupleCoboundary_orient_perm A hr f (Equiv.swap i j)
    have hs : (Equiv.swap i j).sign = (-1 : ℤˣ) := Equiv.Perm.sign_swap hij
    have hp : (if (Equiv.swap i j).sign = (1 : ℤˣ) then (0 : ZMod 2) else 1) = 1 := by
      simp [hs, Units.ext_iff]
    rw [hp] at hsum
    rw [hsum]
    exact zmodBit_add_one _

/-- The new orientation is exactly the unsigned sum of the original oriented
facets, interpreted in F₂, on every injective ordered tuple. -/
theorem Hyper.coboundary_orient {r : ℕ} {V : Type u} (A : Hyper r V) (hr : Even r)
    (f : Fin (r + 1) ↪ V) :
    p1BitToZMod ((A.coboundary hr).orient f) =
      tupleCoboundary (fun t => p1BitToZMod (A.orient t)) f :=
  p3BitToZMod_roundtrip _

/-- Every such coboundary is even, by the intrinsic tuple identity δ²=0. -/
theorem Hyper.isEven_coboundary {r : ℕ} {V : Type u} (A : Hyper r V) (hr : Even r) :
    (A.coboundary hr).IsEven := by
  intro f
  have hfun : (fun t => p1BitToZMod ((A.coboundary hr).orient t)) =
      tupleCoboundary (fun t => p1BitToZMod (A.orient t)) :=
    funext (A.coboundary_orient hr)
  rw [hfun]
  exact tupleCoboundary_tupleCoboundary_zero _ f

/-- Every orientation-preserving vertex injection also preserves coboundaries. -/
theorem Hyper.coboundary_preserves {r : ℕ} {V : Type u} {W : Type v}
    (A : Hyper r V) (B : Hyper r W) (hr : Even r) (e : V ↪ W) (he : Preserves A B e) :
    Preserves (A.coboundary hr) (B.coboundary hr) e := by
  intro f
  apply p1BitToZMod_injective
  rw [Hyper.coboundary_orient, Hyper.coboundary_orient]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg p1BitToZMod (he (facet f i))

/-- Coboundary commutes with arbitrary intrinsic pullbacks. -/
theorem Hyper.coboundary_pullback {r : ℕ} {V : Type u} {W : Type v}
    (A : Hyper r W) (hr : Even r) (e : V ↪ W) :
    (A.pullback e).coboundary hr = (A.coboundary hr).pullback e := by
  apply Hyper.ext
  intro f
  exact (Hyper.coboundary_preserves (A.pullback e) A hr e (fun _ => rfl) f).symm

end Hypertournaments
