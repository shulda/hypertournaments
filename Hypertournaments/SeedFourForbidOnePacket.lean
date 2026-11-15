import Hypertournaments.SeedFourForbidOneRawLogic
import Hypertournaments.SeedFourPacketBridge

/-!
# Soundness of the three forbidden-type Boolean rules

An arbitrary mixed five-tuple (left, i, j, k, right) has normalized
facet packet (beta, -x_jk, x_ik, -x_ij, alpha).

Excluding local type T_{4,1} produces three Boolean constraints:
* T if alpha and beta are different,
* C- if both are false,
* C+ if both are true.

The tiny truth tables below make this fact kernel checked once.
They are independent of the finite seed and of any particular
embedding into an amalgam.
-/

namespace Hypertournaments

private def packetTypeAllowed
    (alpha beta xij xik xjk : Bool) : Prop :=
  let m := mixedPacketPositiveCount4 alpha beta xij xik xjk
  min m (5 - m) = 0 ∨ min m (5 - m) = 2

/-- Incompatible endpoint signs give the T constraint. -/
theorem packet_type_T
    (alpha beta xij xik xjk : Bool)
    (hends : alpha ≠ beta)
    (ht : packetTypeAllowed alpha beta xij xik xjk) :
    ruleT xij xik xjk = true := by
  revert alpha beta xij xik xjk
  unfold packetTypeAllowed
  decide +kernel

/-- Two negative endpoint signs give C-minus. -/
theorem packet_type_Cm
    (xij xik xjk : Bool)
    (ht : packetTypeAllowed false false xij xik xjk) :
    ruleCm xij xik xjk = true := by
  revert xij xik xjk
  unfold packetTypeAllowed
  decide +kernel

/-- Two positive endpoint signs give C-plus. -/
theorem packet_type_Cp
    (xij xik xjk : Bool)
    (ht : packetTypeAllowed true true xij xik xjk) :
    ruleCp xij xik xjk = true := by
  revert xij xik xjk
  unfold packetTypeAllowed
  decide +kernel

/-- A permitted intrinsic mixed five-tuple satisfies the exact
Boolean packet predicate used in the finite SAT-style certificate. -/
theorem allowed_mixed_packet
    {V : Type*} (D : Hyper 4 V) (f : Fin 5 ↪ V)
    (h : localIndex D f ∈ ({0,2} : Set ℕ)) :
    packetTypeAllowed
      (D.orient (facet f 4)) (D.orient (facet f 0))
      (D.orient (facet f 3)) (D.orient (facet f 2))
      (D.orient (facet f 1)) := by
  have hm : localIndex D f =
      min (mixedPacketPositiveCount4
        (D.orient (facet f 4)) (D.orient (facet f 0))
        (D.orient (facet f 3)) (D.orient (facet f 2))
        (D.orient (facet f 1)))
        (5 - mixedPacketPositiveCount4
        (D.orient (facet f 4)) (D.orient (facet f 0))
        (D.orient (facet f 3)) (D.orient (facet f 2))
        (D.orient (facet f 1))) := by
    unfold localIndex
    rw [mixedPacketPositiveCount4_eq D f]
  rcases (show localIndex D f = 0 ∨ localIndex D f = 2 from by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h) with h0 | h2
  · change min (mixedPacketPositiveCount4 _ _ _ _ _)
        (5 - mixedPacketPositiveCount4 _ _ _ _ _) = 0 ∨
      min (mixedPacketPositiveCount4 _ _ _ _ _)
        (5 - mixedPacketPositiveCount4 _ _ _ _ _) = 2
    exact Or.inl (hm.symm.trans h0)
  · change min (mixedPacketPositiveCount4 _ _ _ _ _)
        (5 - mixedPacketPositiveCount4 _ _ _ _ _) = 0 ∨
      min (mixedPacketPositiveCount4 _ _ _ _ _)
        (5 - mixedPacketPositiveCount4 _ _ _ _ _) = 2
    exact Or.inr (hm.symm.trans h2)

/-- T case for a genuine allowed mixed five-tuple. -/
theorem ruleT_of_allowed_mixed
    {V : Type*} (D : Hyper 4 V) (f : Fin 5 ↪ V)
    (h : localIndex D f ∈ ({0,2} : Set ℕ))
    (hends : D.orient (facet f 4) ≠ D.orient (facet f 0)) :
    ruleT (D.orient (facet f 3))
      (D.orient (facet f 2)) (D.orient (facet f 1)) = true := by
  exact packet_type_T _ _ _ _ _ hends (allowed_mixed_packet D f h)

/-- C-minus case for a genuine allowed mixed five-tuple. -/
theorem ruleCm_of_allowed_mixed
    {V : Type*} (D : Hyper 4 V) (f : Fin 5 ↪ V)
    (h : localIndex D f ∈ ({0,2} : Set ℕ))
    (hl : D.orient (facet f 4) = false)
    (hr : D.orient (facet f 0) = false) :
    ruleCm (D.orient (facet f 3))
      (D.orient (facet f 2)) (D.orient (facet f 1)) = true := by
  have hp := allowed_mixed_packet D f h
  rw [hl, hr] at hp
  exact packet_type_Cm _ _ _ hp

/-- C-plus case for a genuine allowed mixed five-tuple. -/
theorem ruleCp_of_allowed_mixed
    {V : Type*} (D : Hyper 4 V) (f : Fin 5 ↪ V)
    (h : localIndex D f ∈ ({0,2} : Set ℕ))
    (hl : D.orient (facet f 4) = true)
    (hr : D.orient (facet f 0) = true) :
    ruleCp (D.orient (facet f 3))
      (D.orient (facet f 2)) (D.orient (facet f 1)) = true := by
  have hp := allowed_mixed_packet D f h
  rw [hl, hr] at hp
  exact packet_type_Cp _ _ _ hp

end Hypertournaments
