import Hypertournaments.FiniteClassAmalgamation
import Hypertournaments.FiveConstrained.CertificatesBasic
import Hypertournaments.FiveConstrained.Mask
import Hypertournaments.LocalTypeIsomorphism
import Hypertournaments.LocalForbiddenFamily
import Mathlib.GroupTheory.Perm.Fin

/-!
# Actual four- and five-constrained ternary classes

The five-packet predicate is intrinsic: an admitted five-packet is isomorphic
to a named representative through an arbitrary vertex permutation. The four
and five palettes are separate, so constraints which are vacuous on small
carriers are not silently strengthened by normalization.
-/

namespace Hypertournaments.FiveConstrained

/-- A named five-packet is allowed up to an actual intrinsic isomorphism. -/
def PacketAllowed (palette : ℕ) (A : Hyper 3 (Fin 5)) : Prop :=
  ∃ t : Fin 12, palette.testBit t.val = true ∧
    ∃ σ : Equiv.Perm (Fin 5),
      Preserves (maskHyper 5 (representative t)) A σ.toEmbedding

/-- All induced five-vertex structures belong to the prescribed palette. -/
def FiveAllowed (palette : ℕ) {V : Type*} (A : Hyper 3 V) : Prop :=
  ∀ e : Fin 5 ↪ V, PacketAllowed palette (A.pullback e)

/-- Bit masks for the original local-index four-types. -/
def fourPalette (palette : ℕ) : Set ℕ := {d | palette.testBit d = true}

/-- Separate conditions on four- and five-vertex induced substructures. -/
def Constrained (four five : ℕ) {V : Type*} (A : Hyper 3 V) : Prop :=
  Admissible (fourPalette four) A ∧ FiveAllowed five A

/-- The corresponding finite class with the existing intrinsic embeddings. -/
def constrainedClass (four five : ℕ) : FiniteClass 3 :=
  fun _ A => Constrained four five A

/-- The normalized presentation derives its four-palette from the five-types. -/
def normalizedClass (five : ℕ) : FiniteClass 3 :=
  constrainedClass (certificateSupport4 five) five

theorem PacketAllowed.map {palette : ℕ} {A B : Hyper 3 (Fin 5)}
    (σ : Equiv.Perm (Fin 5)) (hAB : Preserves A B σ.toEmbedding)
    (hA : PacketAllowed palette A) : PacketAllowed palette B := by
  obtain ⟨t, ht, π, hπ⟩ := hA
  refine ⟨t, ht, σ * π, ?_⟩
  intro u
  have heq : u.trans (σ * π).toEmbedding =
      (u.trans π.toEmbedding).trans σ.toEmbedding := by
    ext i
    rfl
  rw [heq]
  exact (hAB (u.trans π.toEmbedding)).trans (hπ u)

/-- All injective tuples are covered by their increasing presentation and the
actual signed vertex permutation. -/
theorem fiveAllowed_iff_increasing {k : ℕ} (palette : ℕ)
    (A : Hyper 3 (Fin k)) :
    FiveAllowed palette A ↔
      ∀ e : Fin 5 ↪ Fin k, StrictMono (e : Fin 5 → Fin k) →
        PacketAllowed palette (A.pullback e) := by
  constructor
  · exact fun h e _ => h e
  · intro h e
    let τ : Equiv.Perm (Fin 5) := Tuple.sort (e : Fin 5 → Fin k)
    let g : Fin 5 ↪ Fin k := τ.toEmbedding.trans e
    have hg : StrictMono (g : Fin 5 → Fin k) :=
      (Tuple.monotone_sort (e : Fin 5 → Fin k)).strictMono_of_injective g.injective
    exact PacketAllowed.map τ (fun _ => rfl) (h g hg)

theorem fourAllowed_iff_increasing {k : ℕ} (palette : ℕ)
    (A : Hyper 3 (Fin k)) :
    Admissible (fourPalette palette) A ↔
      ∀ e : Fin 4 ↪ Fin k, StrictMono (e : Fin 4 → Fin k) →
        palette.testBit (localIndex A e) = true := by
  constructor
  · exact fun h e _ => h e
  · intro h e
    let τ : Equiv.Perm (Fin 4) := Tuple.sort (e : Fin 4 → Fin k)
    let g : Fin 4 ↪ Fin k := τ.toEmbedding.trans e
    have hg : StrictMono (g : Fin 4 → Fin k) :=
      (Tuple.monotone_sort (e : Fin 4 → Fin k)).strictMono_of_injective g.injective
    have hidx := localIndex_perm_all A e τ
    change palette.testBit (localIndex A e) = true
    rw [← hidx]
    exact h g hg

theorem constrained_iff_increasing {k : ℕ} (four five : ℕ)
    (A : Hyper 3 (Fin k)) :
    Constrained four five A ↔
      (∀ e : Fin 4 ↪ Fin k, StrictMono (e : Fin 4 → Fin k) →
        four.testBit (localIndex A e) = true) ∧
      (∀ e : Fin 5 ↪ Fin k, StrictMono (e : Fin 5 → Fin k) →
        PacketAllowed five (A.pullback e)) := by
  exact and_congr (fourAllowed_iff_increasing four A) (fiveAllowed_iff_increasing five A)

/-- Only the three genuine four-types affect the intrinsic class. -/
theorem constrained_iff_of_four_agree {four four' five : ℕ}
    (h : ∀ d : ℕ, d ≤ 2 → (four.testBit d = true ↔ four'.testBit d = true))
    {V : Type*} (A : Hyper 3 V) :
    Constrained four five A ↔ Constrained four' five A := by
  constructor
  · intro hA
    refine ⟨?_, hA.2⟩
    intro e
    exact (h (localIndex A e) (localIndex_le_central A e)).mp (hA.1 e)
  · intro hA
    refine ⟨?_, hA.2⟩
    intro e
    exact (h (localIndex A e) (localIndex_le_central A e)).mpr (hA.1 e)

theorem FiveAllowed.of_preserves {palette : ℕ} {V W : Type*}
    {A : Hyper 3 V} {B : Hyper 3 W} (e : V ↪ W)
    (hAB : Preserves A B e) (hB : FiveAllowed palette B) :
    FiveAllowed palette A := by
  intro t
  obtain ⟨i, hi, σ, hσ⟩ := hB (t.trans e)
  refine ⟨i, hi, σ, ?_⟩
  intro s
  exact (hAB ((s.trans σ.toEmbedding).trans t)).symm.trans (hσ s)

theorem Constrained.of_preserves {four five : ℕ} {V W : Type*}
    {A : Hyper 3 V} {B : Hyper 3 W} (e : V ↪ W)
    (hAB : Preserves A B e) (hB : Constrained four five B) :
    Constrained four five A := by
  refine ⟨?_, FiveAllowed.of_preserves e hAB hB.2⟩
  exact admissible_of_preserves hAB hB.1

theorem constrainedClass_hereditary (four five : ℕ) :
    (constrainedClass four five).Hereditary := by
  intro a b A B e hAB hB
  exact Constrained.of_preserves e hAB hB

theorem normalizedClass_hereditary (five : ℕ) :
    (normalizedClass five).Hereditary :=
  constrainedClass_hereditary _ _

theorem constrainedClass_hasJEP_of_hasAP {four five : ℕ}
    (hAP : (constrainedClass four five).HasAP) :
    (constrainedClass four five).HasJEP :=
  hAP.hasJEP (constrainedClass_hereditary four five) (by decide)

end Hypertournaments.FiveConstrained
