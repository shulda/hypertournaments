import Hypertournaments.OnePointLink
import Hypertournaments.EPPASourceTransport
import Hypertournaments.ConeNaturality
import Hypertournaments.LocalForbiddenFamily
import Hypertournaments.EvenSwitching
import Hypertournaments.UnrestrictedAmalgamation
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext

/-!
# Ordinary finite EPPA transfers one arity down

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`prop:even-eppa-transfer`. Extend the partial maps which explicitly fix
the cone root, then restrict their upper automorphisms to its full link.
The upper witness itself need not be even.
-/

universe u v

namespace Hypertournaments

/-- The old cone vertices embed in the complement of the root's image. -/
def coneLinkEmbedding {V : Type u} {W : Type v} (e : Option V ↪ W) :
    V ↪ {x : W // x ≠ e none} where
  toFun x := ⟨e (some x), fun h => Option.some_ne_none x (e.injective h)⟩
  inj' := by
    intro x y h
    exact Option.some.inj (e.injective (congrArg Subtype.val h))

@[simp] theorem coneLinkEmbedding_apply {V : Type u} {W : Type v}
    (e : Option V ↪ W) (x : V) : (coneLinkEmbedding e x : W) = e (some x) := rfl

/-- The link of any finite witness for the even cone is a genuine ordinary
finite witness for the lower structure, with its original source carrier. -/
theorem evenCone_witness_link {r : ℕ} {V : Type u} {W : Type v} [Finite V]
    (A : Hyper r V) (hr : Even r) (B : Hyper (r + 1) W) (e : Option V ↪ W)
    (hw : (A.evenCone hr).IsEPPAWitness B e) :
    A.IsEPPAWitness (B.onePointLink (e none)) (coneLinkEmbedding e) := by
  let : Finite W := hw.finite
  refine ⟨inferInstance, ?_, ?_⟩
  · intro t
    have ht : onePointTuple (pointComplementEmbedding (e none)) (e none)
        (point_not_mem_complement (e none)) (t.trans (coneLinkEmbedding e)) =
        (onePointTuple Function.Embedding.some none
          (by rintro ⟨x, hx⟩; exact Option.some_ne_none x hx) t).trans e := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    change B.orient (onePointTuple _ (e none) _ (t.trans (coneLinkEmbedding e))) = _
    rw [ht, hw.preserves]
    exact A.evenCone_root_orient hr t
  · intro p
    let P := A.pullback (subsetEmbedding p.source)
    let i : p.source ↪ V := subsetEmbedding p.source
    let j : p.source ↪ V := p.equiv.toEmbedding.trans (subsetEmbedding p.target)
    have hi : Preserves P A i := by intro t; rfl
    have hj : Preserves P A j := by intro t; exact p.preserves t
    obtain ⟨g, hg⟩ := hw.extend_isomorphism (P.evenCone hr)
      (Function.Embedding.optionMap i) (Function.Embedding.optionMap j)
      (P.evenCone_preserves A hr i hi) (P.evenCone_preserves A hr j hj)
    have hroot : (g : Equiv.Perm W) (e none) = e none := hg none
    refine ⟨g.onePointLink (e none) hroot, ?_⟩
    intro x
    apply Subtype.ext
    exact hg (some x)

/-- EPPA for all upper-arity hypertournaments implies EPPA for the
unrestricted preceding even arity. -/
theorem unrestricted_eppa_one_arity_down {r : ℕ} (hr : Even r) (_hr2 : 2 ≤ r)
    (hK : HasEPPA (emptyForbiddenFamily (r + 1))) :
    HasEPPA (emptyForbiddenFamily r) := by
  intro a A _hA
  obtain ⟨b, B, e, _, hw⟩ := hK.exists_witness (A.evenCone hr)
    (omits_emptyForbiddenFamily _)
  obtain ⟨m, C, j, hC⟩ := (evenCone_witness_link A hr B e hw).hasFiniteEPPAWitness
  exact ⟨m, C, j, omits_emptyForbiddenFamily C, hC⟩

/-- EPPA even within the upper even class implies unrestricted EPPA in
the preceding even arity. The witness link need not be even. -/
theorem even_eppa_one_arity_down {r : ℕ} (hr : Even r) (_hr2 : 2 ≤ r)
    (hK : HasEPPA (localForbiddenFamily (r + 1) (switchingAllowed (r + 1)))) :
    HasEPPA (emptyForbiddenFamily r) := by
  have hodd : Odd (r + 1) := by
    obtain ⟨k, hk⟩ := hr
    exact ⟨k, by omega⟩
  intro a A _hA
  have hcone : Omits (localForbiddenFamily (r + 1) (switchingAllowed (r + 1)))
      (A.evenCone hr) :=
    (omits_localForbiddenFamily_iff_admissible _ _).mpr
      (((A.evenCone hr).admissible_switching_iff_isEven hodd).mpr (A.evenCone_isEven hr))
  obtain ⟨b, B, e, _, hw⟩ := hK.exists_witness (A.evenCone hr) hcone
  obtain ⟨m, C, j, hC⟩ := (evenCone_witness_link A hr B e hw).hasFiniteEPPAWitness
  exact ⟨m, C, j, omits_emptyForbiddenFamily C, hC⟩

/-- Literal odd-arity formulation of the article's transfer theorem. -/
theorem eppa_one_arity_down (n : ℕ) (hn : Odd n) (hn3 : 3 ≤ n)
    (hK : HasEPPA (localForbiddenFamily n (switchingAllowed n)) ∨
      HasEPPA (emptyForbiddenFamily n)) : HasEPPA (emptyForbiddenFamily (n - 1)) := by
  obtain ⟨k, hk⟩ := hn
  have hnEq : n = 2 * k + 1 := by omega
  subst n
  have hr : Even (2 * k) := ⟨k, by omega⟩
  have hr2 : 2 ≤ 2 * k := by omega
  cases hK with
  | inl h => simpa using even_eppa_one_arity_down hr hr2 h
  | inr h => simpa using unrestricted_eppa_one_arity_down hr hr2 h

end Hypertournaments
