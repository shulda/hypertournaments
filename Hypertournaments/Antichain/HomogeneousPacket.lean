import Hypertournaments.Antichain.SumInduced
import Hypertournaments.PartialHyper
import Hypertournaments.GeneralLocalIndexInvariant
import Hypertournaments.OddToggleP1Homogeneous

/-!
# Intrinsic homogeneous packets

The local index depends only on the vertex set of a packet. A uniform change
of all orientation bits preserves the homogeneous local type. Both facts are
uniform in the arity and apply in particular to four-vertex ternary packets.
-/

namespace Hypertournaments.Antichain

/-- Two enumerations of the same finite vertex set differ by a coordinate
permutation. -/
theorem tuple_perm_of_tupleVertices_eq {k : ℕ} {V : Type*} [DecidableEq V]
    (f g : Fin k ↪ V) (h : tupleVertices f = tupleVertices g) :
    ∃ σ : Equiv.Perm (Fin k), σ.toEmbedding.trans f = g := by
  classical
  have hex (i : Fin k) : ∃ j : Fin k, f j = g i := by
    apply (tupleVertices_mem_range f (g i)).mp
    rw [h]
    exact (tupleVertices_mem_range g (g i)).mpr ⟨i, rfl⟩
  choose s hs using hex
  have hinj : Function.Injective s := by
    intro i j hij
    apply g.injective
    rw [← hs i, ← hs j, hij]
  let σ : Equiv.Perm (Fin k) := Equiv.ofBijective s
    ⟨hinj, Finite.surjective_of_injective hinj⟩
  refine ⟨σ, ?_⟩
  apply Function.Embedding.ext
  exact hs

/-- The intrinsic local index does not depend on the enumeration of the
packet's vertex set. -/
theorem localIndex_eq_of_tupleVertices_eq {n : ℕ} {V : Type*} [DecidableEq V]
    (A : Hyper n V) (f g : Fin (n + 1) ↪ V)
    (h : tupleVertices f = tupleVertices g) : localIndex A f = localIndex A g := by
  obtain ⟨σ, rfl⟩ := tuple_perm_of_tupleVertices_eq f g h
  exact (localIndex_perm_all A f σ).symm

/-- A uniform field shift of orientation bits makes the same uniform Boolean
change in every normalized facet. -/
theorem normalizedFacet_eq_xor_of_bit_shift {n : ℕ} {V W : Type*}
    (A : Hyper n V) (B : Hyper n W) (e : V ↪ W) (c : ZMod 2)
    (h : ∀ t : Fin n ↪ V, bit (B.orient (t.trans e)) = bit (A.orient t) + c)
    (f : Fin (n + 1) ↪ V) (i : Fin (n + 1)) :
    normalizedFacet B (f.trans e) i = (normalizedFacet A f i ^^ boolOf c) := by
  apply bit_injective
  simp only [normalizedFacet, bit_xor, bit_boolOf]
  change bit (B.orient ((facet f i).trans e)) + bit (decide (i.val % 2 = 1)) =
    (bit (A.orient (facet f i)) + bit (decide (i.val % 2 = 1))) + c
  rw [h]
  ac_rfl

/-- A uniform field shift of every orientation bit preserves the homogeneous
local type. The embedding may have any ambient target carrier. -/
theorem localIndex_zero_iff_of_bit_shift {n : ℕ} {V W : Type*}
    (A : Hyper n V) (B : Hyper n W) (e : V ↪ W) (c : ZMod 2)
    (h : ∀ t : Fin n ↪ V, bit (B.orient (t.trans e)) = bit (A.orient t) + c)
    (f : Fin (n + 1) ↪ V) :
    localIndex A f = 0 ↔ localIndex B (f.trans e) = 0 := by
  rw [localIndex_zero_iff_normalized_constant, localIndex_zero_iff_normalized_constant]
  have hfacet := normalizedFacet_eq_xor_of_bit_shift A B e c h f
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b ^^ boolOf c, ?_⟩
    intro i
    rw [hfacet i, hb i]
  · rintro ⟨b, hb⟩
    refine ⟨b ^^ boolOf c, ?_⟩
    intro i
    rw [← hb i, hfacet i]
    simp

end Hypertournaments.Antichain
