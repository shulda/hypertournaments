import Hypertournaments.OddToggleP3PotentialPresentation

/-!
# Explicit finite block-transversal potential schema for the p3 exception

The p3 probabilistic non-amalgamation witness uses m=n-1 ordered
blocks with t old vertices per block, one fresh vertex on each side,
and three families of potential bits W, L, R. The random bits are
abstract functions at this stage; no sampling or probabilistic
independence is assumed.

W is supported on m-element full block transversals.
L (or R) is supported on (m-1)-element old transversals with
exactly one missing block in a designated eligible half.

The actual one-point side potential is defined on finite subsets
of an arbitrary linearly ordered ambient vertex type, using a
specified old-base embedding and a fresh vertex.

This module supplies concrete definitions and the exact agreement
of left/right potential tables on old-only subsets. The later age
proof must show the corresponding intrinsic hypertournaments omit
homogeneous packets for every choice of these potential bits.
-/

namespace Hypertournaments

/-- Numeric index of the contiguous block containing an old vertex.
In the nonempty-block case t>0 and v< m*t, this lies below m. -/
def p3BlockNumber (t : ℕ) {m : ℕ} (v : Fin (m*t)) : ℕ :=
  v.val / t

/-- Number of selected old vertices belonging to a specified block. -/
def p3BlockOccupancy (m t : ℕ)
    (U : Finset (Fin (m*t))) (i : Fin m) : ℕ :=
  (U.filter (fun v => p3BlockNumber t v = i.val)).card

/-- An old m-set meeting each of the m blocks exactly once. -/
def p3IsBlockTransversal (m t : ℕ)
    (U : Finset (Fin (m*t))) : Prop :=
  U.card = m ∧ ∀ i : Fin m, p3BlockOccupancy m t U i = 1

/-- An old (m-1)-set meeting all blocks except exactly one
eligible missing index, with one old vertex in every present block. -/
def p3IsEligibleMissingTransversal (m t : ℕ)
    (eligible : Finset (Fin m))
    (U : Finset (Fin (m*t))) : Prop :=
  U.card = m-1 ∧
    ∃ i : Fin m, i ∈ eligible ∧
      p3BlockOccupancy m t U i = 0 ∧
      ∀ j : Fin m, j ≠ i → p3BlockOccupancy m t U j = 1

/-- Old part of a side subset under an explicit embedding of the base. -/
def p3SideOldPart {a : ℕ} {V : Type*}
    [DecidableEq V] (old : Fin a ↪ V) (Q : Finset V) :
    Finset (Fin a) :=
  Finset.univ.filter (fun v => old v ∈ Q)

/-- Restrict an arbitrary family of base potential bits W to
the full m-block transversals, setting all other values to zero. -/
noncomputable def p3BasePotential (m t : ℕ)
    (W : Finset (Fin (m*t)) → ZMod 2) :
    Finset (Fin (m*t)) → ZMod 2 := by
  classical
  exact fun U => if p3IsBlockTransversal m t U then W U else 0

/-- Actual potential on one side, on every finite subset Q of
the ambient side vertex set V. Its old part is read through the
base embedding. If the new vertex belongs to Q, only an eligible
one-block-missing transversal has a potentially nonzero coefficient.
Otherwise Q must be a full transversal. -/
noncomputable def p3SidePotential
    (m t : ℕ) {V : Type*} [DecidableEq V]
    (old : Fin (m*t) ↪ V) (fresh : V)
    (eligible : Finset (Fin m))
    (W L : Finset (Fin (m*t)) → ZMod 2) :
    Finset V → ZMod 2 := by
  classical
  exact fun Q =>
    let U := p3SideOldPart old Q
    if fresh ∈ Q then
      if p3IsEligibleMissingTransversal m t eligible U then L U else 0
    else
      if p3IsBlockTransversal m t U then W U else 0

/-- The resulting genuine intrinsic (m+1)-hypertournament from
a side potential, with no age assertion or probabilistic premise. -/
noncomputable def p3SideHyper
    (m t : ℕ) {V : Type*} [LinearOrder V]
    (old : Fin (m*t) ↪ V) (fresh : V)
    (eligible : Finset (Fin m))
    (W L : Finset (Fin (m*t)) → ZMod 2) :
    Hyper (m+1) V :=
  Hyper.fromOrderedSigns
    (fun Q => p3ZMod2ToBool
      (coboundary (p3SidePotential m t old fresh eligible W L) Q))

/-- With the fresh point absent, the side potential is precisely
the old base transversal table, independent of the eligible half
and independent of the fresh side-link potential L. -/
theorem p3SidePotential_oldOnly
    (m t : ℕ) {V : Type*} [DecidableEq V]
    (old : Fin (m*t) ↪ V) (fresh : V)
    (eligible : Finset (Fin m))
    (W L : Finset (Fin (m*t)) → ZMod 2)
    (Q : Finset V) (h : fresh ∉ Q) :
    p3SidePotential m t old fresh eligible W L Q =
      p3BasePotential m t W (p3SideOldPart old Q) := by
  classical
  simp [p3SidePotential, p3BasePotential, h]

/-- The left/right potential families agree identically on
old-only subsets when they use the same old base embedding and W. -/
theorem p3TwoSidePotentials_agree_oldOnly
    (m t : ℕ) {V : Type*} [DecidableEq V]
    (old : Fin (m*t) ↪ V) (fresh : V)
    (eligibleL eligibleR : Finset (Fin m))
    (W L R : Finset (Fin (m*t)) → ZMod 2)
    (Q : Finset V) (h : fresh ∉ Q) :
    p3SidePotential m t old fresh eligibleL W L Q =
      p3SidePotential m t old fresh eligibleR W R Q := by
  rw [p3SidePotential_oldOnly m t old fresh eligibleL W L Q h]
  rw [p3SidePotential_oldOnly m t old fresh eligibleR W R Q h]

/-- The induced old-part operation is exact on the image of the
old-base embedding, with no loss or spurious vertex. -/
theorem p3SideOldPart_image
    (m t : ℕ) {V : Type*} [DecidableEq V]
    (old : Fin (m*t) ↪ V)
    (U : Finset (Fin (m*t))) :
    p3SideOldPart old (U.image old) = U := by
  classical
  ext v
  simp only [p3SideOldPart, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hv
    obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hv
    have hveq : w = v := old.injective heq
    simpa [hveq] using hw
  · intro hv
    exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

end Hypertournaments
