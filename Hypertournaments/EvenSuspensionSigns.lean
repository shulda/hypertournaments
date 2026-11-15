import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Hypertournaments.CanonicalSignPresentation

/-!
# A concrete ordered-sign table for even two-coordinate suspension

Let A be an intrinsic n-hypertournament on Fin k. Prepend m ordered
padding vertices 0,...,m-1 to the k old vertices. A high (n+2)-set
receives the old sign precisely when it contains exactly two pads;
all other high sets receive positive sign.

We make this construction as a genuine finite sign table on
Fin(m+k), rather than an informal conditional on an unspecified
ordered subset. The key finite-set lemmas establish that a packet
consisting of two distinct pads and an old set has exactly two pads,
and that the old portion is exactly the original old set. Consequently,
the suspension sign table recovers A's canonical old sign on all
such subsets. Intrinsic tuple recovery and admissibility of the
suspension remain separate proof obligations.
-/

namespace Hypertournaments

/-- Map a pad vertex into the first m positions of the lifted set. -/
def evenPadShift (m k : ℕ) : Fin m ↪ Fin (m + k) where
  toFun z := ⟨z.val, by omega⟩
  inj' := by
    intro x y h
    have hv := congrArg (fun z : Fin (m + k) => z.val) h
    apply Fin.ext
    exact hv

/-- Map an old vertex into the last k positions of the lifted set. -/
def evenOldShift (m k : ℕ) : Fin k ↪ Fin (m + k) where
  toFun z := ⟨m + z.val, by omega⟩
  inj' := by
    intro x y h
    apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp at hv
    omega

/-- Pad vertices cannot coincide with images of old vertices. -/
theorem evenPadShift_ne_oldShift (m k : ℕ)
    (x : Fin m) (u : Fin k) :
    evenPadShift m k x ≠ evenOldShift m k u := by
  intro h
  have hv := congrArg Fin.val h
  change x.val = m + u.val at hv
  omega

/-- Extract the pad indices present in a subset of the padded set. -/
def evenPadProjection (m k : ℕ)
    (Q : Finset (Fin (m + k))) : Finset (Fin m) :=
  Finset.univ.filter (fun x => evenPadShift m k x ∈ Q)

/-- Extract old vertex indices present in a subset of the padded set. -/
def evenOldProjection (m k : ℕ)
    (Q : Finset (Fin (m + k))) : Finset (Fin k) :=
  Finset.univ.filter (fun x => evenOldShift m k x ∈ Q)

/-- Two specified pads and an arbitrary old finite vertex set. -/
def evenPaddedPacket (m k : ℕ)
    (x y : Fin m) (Q : Finset (Fin k)) :
    Finset (Fin (m + k)) :=
  insert (evenPadShift m k x)
    (insert (evenPadShift m k y) (Q.image (evenOldShift m k)))

/-- The old projection of a packet containing two pads and the image
of an old vertex subset is exactly the original old subset. -/
theorem evenOldProjection_paddedPacket
    (m k : ℕ) (x y : Fin m) (Q : Finset (Fin k)) :
    evenOldProjection m k (evenPaddedPacket m k x y Q) = Q := by
  ext u
  simp only [evenOldProjection, Finset.mem_filter, Finset.mem_univ,
    true_and, evenPaddedPacket, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (hx | hy | ⟨v, hv, hvu⟩)
    · exact False.elim (evenPadShift_ne_oldShift m k x u hx.symm)
    · exact False.elim (evenPadShift_ne_oldShift m k y u hy.symm)
    · have he : v = u := (evenOldShift m k).injective hvu
      simpa [he] using hv
  · intro hu
    exact Or.inr (Or.inr ⟨u, hu, rfl⟩)

/-- The pad projection of a packet containing two pads and old
vertices is precisely the (unordered) pair of selected pad indices. -/
theorem evenPadProjection_paddedPacket
    (m k : ℕ) (x y : Fin m) (Q : Finset (Fin k)) :
    evenPadProjection m k (evenPaddedPacket m k x y Q) =
      ({x, y} : Finset (Fin m)) := by
  ext z
  simp only [evenPadProjection, Finset.mem_filter, Finset.mem_univ,
    true_and, evenPaddedPacket, Finset.mem_insert, Finset.mem_image,
    Finset.mem_singleton]
  constructor
  · rintro (hx | hy | ⟨u, hu, huz⟩)
    · exact Or.inl ((evenPadShift m k).injective hx)
    · exact Or.inr ((evenPadShift m k).injective hy)
    · exact False.elim (evenPadShift_ne_oldShift m k z u huz.symm)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)

/-- Two distinct selected pads really constitute exactly two
padding vertices in the corresponding high-arity packet. -/
theorem evenPadProjection_paddedPacket_card
    (m k : ℕ) (x y : Fin m) (Q : Finset (Fin k))
    (hxy : x ≠ y) :
    (evenPadProjection m k (evenPaddedPacket m k x y Q)).card = 2 := by
  rw [evenPadProjection_paddedPacket]
  simp [hxy]

/-- Literal finite sign table of the even two-coordinate suspension.
A source sign is used only on high sets with exactly two pads. -/
def evenSuspensionSignTable
    {n : ℕ} (m k : ℕ) (A : Hyper n (Fin k))
    (Q : Finset (Fin (m + k))) : Bool :=
  if (evenPadProjection m k Q).card = 2 then
    A.canonicalSignTable (evenOldProjection m k Q)
  else true

/-- The suspended sign on any two-pad old-subset packet is exactly
the canonical sign of the old subset, regardless of its size. -/
theorem evenSuspensionSignTable_twoPads
    {n : ℕ} (m k : ℕ) (A : Hyper n (Fin k))
    (x y : Fin m) (Q : Finset (Fin k)) (hxy : x ≠ y) :
    evenSuspensionSignTable m k A (evenPaddedPacket m k x y Q) =
      A.canonicalSignTable Q := by
  unfold evenSuspensionSignTable
  rw [evenPadProjection_paddedPacket_card m k x y Q hxy]
  simp [evenOldProjection_paddedPacket]

/-- The intrinsic lifted (n+2)-hypertournament defined from this
ordered sign table. No extra linear order is retained in its language. -/
def Hyper.evenSuspension
    {n : ℕ} (m k : ℕ) (A : Hyper n (Fin k)) :
    Hyper (n + 2) (Fin (m + k)) :=
  Hyper.fromOrderedSigns (evenSuspensionSignTable m k A)

end Hypertournaments
