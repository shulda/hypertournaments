import Hypertournaments.Automorphism
import Hypertournaments.NormalizedPacketSign
import Hypertournaments.FacetOrientationRecovery
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour

/-!
# The actual Klein action on four equal packet entries

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`prop:higharity-eppa-obstruction`. Even permutations in the standard Klein
subgroup on four letters are extended by the identity outside the chosen
four packet vertices. Equality of their normalized facet values proves
preservation of every oriented tuple, not only of the base reduct.
-/

namespace Hypertournaments

/-- The standard Klein subgroup of the alternating group on four letters. -/
abbrev PacketKleinGroup : Type := alternatingGroup.kleinFour (Fin 4)

instance packetKlein_isKleinFour : IsKleinFour PacketKleinGroup :=
  alternatingGroup.kleinFour_isKleinFour (by simp)

/-- Its faithful underlying action on the four letters. -/
def packetKleinFourPerm : PacketKleinGroup →* Equiv.Perm (Fin 4) :=
  (alternatingGroup (Fin 4)).subtype.comp (alternatingGroup.kleinFour (Fin 4)).subtype

theorem packetKleinFourPerm_injective : Function.Injective packetKleinFourPerm := by
  intro a b h
  exact Subtype.ext (Subtype.ext h)

/-- The four distinguished packet entries are base vertices, so the final
packet vertex is fixed by the extended action. -/
def packetFourEmbedding {n : ℕ} (w : Fin 4 ↪ Fin n) : Fin 4 ↪ Fin (n + 1) :=
  ⟨fun i => (w i).castSucc, (Fin.castSucc_injective n).comp w.injective⟩

/-- Extend the standard Klein permutations by the identity. -/
noncomputable def packetKleinPerm {n : ℕ} (w : Fin 4 ↪ Fin n) :
    PacketKleinGroup →* Equiv.Perm (Fin (n + 1)) :=
  (Equiv.Perm.viaEmbeddingHom (packetFourEmbedding w)).comp packetKleinFourPerm

theorem packetKleinPerm_injective {n : ℕ} (w : Fin 4 ↪ Fin n) :
    Function.Injective (packetKleinPerm w) :=
  (Equiv.Perm.viaEmbeddingHom_injective (packetFourEmbedding w)).comp
    packetKleinFourPerm_injective

@[simp] theorem packetKleinPerm_four {n : ℕ} (w : Fin 4 ↪ Fin n)
    (a : PacketKleinGroup) (i : Fin 4) :
    packetKleinPerm w a ((w i).castSucc) =
      (w (packetKleinFourPerm a i)).castSucc :=
  Equiv.Perm.viaEmbedding_apply _ _ i

theorem packetKleinPerm_outside {n : ℕ} (w : Fin 4 ↪ Fin n)
    (a : PacketKleinGroup) (i : Fin (n + 1))
    (hi : i ∉ Set.range (packetFourEmbedding w)) : packetKleinPerm w a i = i :=
  Equiv.Perm.viaEmbedding_apply_of_notMem _ _ i hi

@[simp] theorem packetKleinPerm_last {n : ℕ} (w : Fin 4 ↪ Fin n)
    (a : PacketKleinGroup) : packetKleinPerm w a (Fin.last n) = Fin.last n := by
  apply packetKleinPerm_outside
  rintro ⟨i, hi⟩
  have hv := congrArg Fin.val hi
  change (w i).val = n at hv
  exact (Nat.ne_of_lt (w i).isLt) hv

theorem packetKleinPerm_base_outside {n : ℕ} (w : Fin 4 ↪ Fin n)
    (a : PacketKleinGroup) (i : Fin n) (hi : i ∉ Set.range w) :
    packetKleinPerm w a i.castSucc = i.castSucc := by
  apply packetKleinPerm_outside
  rintro ⟨j, hj⟩
  exact hi ⟨j, Fin.castSucc_injective n hj⟩

@[simp] theorem packetKleinPerm_sign {n : ℕ} (w : Fin 4 ↪ Fin n)
    (a : PacketKleinGroup) : (packetKleinPerm w a).sign = 1 := by
  classical
  change ((packetKleinFourPerm a).viaEmbedding (packetFourEmbedding w)).sign = 1
  rw [Equiv.Perm.viaEmbedding, Equiv.Perm.sign_extendDomain]
  exact (Equiv.Perm.mem_alternatingGroup.mp a.val.property)

/-- Four equal normalized entries are preserved by the full extended Klein
action, including the distinguished final vertex and every oriented facet. -/
theorem packetKleinPerm_preserves {n : ℕ} (P : Hyper n (Fin (n + 1)))
    (w : Fin 4 ↪ Fin n)
    (hbits : ∀ i j : Fin 4,
      normalizedFacet P (Function.Embedding.refl _) (w i).castSucc =
        normalizedFacet P (Function.Embedding.refl _) (w j).castSucc)
    (a : PacketKleinGroup) : Preserves P P (packetKleinPerm w a).toEmbedding := by
  apply preserves_of_normalizedFacets
  intro i
  have h := normalizedFacet_perm P (Function.Embedding.refl _) (packetKleinPerm w a) i
  simp only [Function.Embedding.trans_refl, packetKleinPerm_sign, ite_true] at h
  rw [h]
  by_cases hi : i ∈ Set.range (packetFourEmbedding w)
  · obtain ⟨j, rfl⟩ := hi
    rw [show packetFourEmbedding w j = (w j).castSucc from rfl, packetKleinPerm_four]
    exact hbits _ _
  · rw [packetKleinPerm_outside w a i hi]

/-- The actual orientation-preserving Klein action on the whole packet. -/
noncomputable def packetKleinAutomorphisms {n : ℕ} (P : Hyper n (Fin (n + 1)))
    (w : Fin 4 ↪ Fin n)
    (hbits : ∀ i j : Fin 4,
      normalizedFacet P (Function.Embedding.refl _) (w i).castSucc =
        normalizedFacet P (Function.Embedding.refl _) (w j).castSucc) :
    PacketKleinGroup →* P.Aut where
  toFun a := ⟨packetKleinPerm w a, packetKleinPerm_preserves P w hbits a⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)

theorem packetKleinAutomorphisms_injective {n : ℕ} (P : Hyper n (Fin (n + 1)))
    (w : Fin 4 ↪ Fin n)
    (hbits : ∀ i j : Fin 4,
      normalizedFacet P (Function.Embedding.refl _) (w i).castSucc =
        normalizedFacet P (Function.Embedding.refl _) (w j).castSucc) :
    Function.Injective (packetKleinAutomorphisms P w hbits) := by
  intro a b h
  exact packetKleinPerm_injective w (congrArg Subtype.val h)

@[simp] theorem packetKleinAutomorphisms_last {n : ℕ}
    (P : Hyper n (Fin (n + 1))) (w : Fin 4 ↪ Fin n)
    (hbits : ∀ i j : Fin 4,
      normalizedFacet P (Function.Embedding.refl _) (w i).castSucc =
        normalizedFacet P (Function.Embedding.refl _) (w j).castSucc)
    (a : PacketKleinGroup) :
    ((packetKleinAutomorphisms P w hbits a : P.Aut) : Equiv.Perm _) (Fin.last n) = Fin.last n :=
  packetKleinPerm_last w a

theorem packetKleinAutomorphisms_base_outside {n : ℕ}
    (P : Hyper n (Fin (n + 1))) (w : Fin 4 ↪ Fin n)
    (hbits : ∀ i j : Fin 4,
      normalizedFacet P (Function.Embedding.refl _) (w i).castSucc =
        normalizedFacet P (Function.Embedding.refl _) (w j).castSucc)
    (a : PacketKleinGroup) (i : Fin n) (hi : i ∉ Set.range w) :
    ((packetKleinAutomorphisms P w hbits a : P.Aut) : Equiv.Perm _) i.castSucc = i.castSucc :=
  packetKleinPerm_base_outside w a i hi

end Hypertournaments
