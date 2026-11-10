import Hypertournaments.OddToggleP1OmissionFacets
import Hypertournaments.AllArityCanonicalAdmissibility

/-!
# Every p1 one-point packet omits exactly one vertex

In arity n=4k+5, each actual one-point side has 4k+7 vertices.
Every local (n+1)-packet therefore consists of all side vertices
except one. If the omitted vertex is the new last vertex, the packet
is the entire old common base. Otherwise it is exactly a genuine
side packet omitting one original old vertex.

This exhaustive geometric dichotomy reduces full side admissibility
to one inherited base packet and an all-arity old-omission row check.
-/

namespace Hypertournaments

/-- In Fin(a+1), every subset with precisely a elements is
the complete universe with one vertex deleted. -/
theorem p1OnePointSubset_eq_erase
    (a : ℕ) (Q : Finset (Fin (a+1)))
    (hQ : Q.card = a) :
    ∃ v : Fin (a+1), Q = Finset.univ.erase v := by
  have hmiss : ((Finset.univ : Finset (Fin (a+1))) \ Q).card = 1 := by
    rw [Finset.card_sdiff]
    simp only [Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hQ]
    omega
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hmiss
  refine ⟨v, ?_⟩
  ext x
  have hiff : x ∈ Q ↔ x ≠ v := by
    have hm : x ∈ (Finset.univ \ Q : Finset (Fin (a+1))) ↔ x = v := by
      rw [hv]
      simp
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hm
    tauto
  simpa only [Finset.mem_erase, Finset.mem_univ, and_true] using hiff

/-- Actual p1 one-point packets are either the full old base or
a packet missing precisely one old base vertex. -/
theorem p1SideSubset_old_or_omit (k : ℕ)
    (Q : Finset (Fin (4*k+6+1)))
    (hQ : Q.card = 4*k+6) :
    Q = (Finset.univ : Finset (Fin (4*k+6+1))).erase
          (Fin.last (4*k+6)) ∨
      ∃ v : Fin (4*k+6), Q = p1SidePacketOmitOld k v := by
  obtain ⟨x, hx⟩ := p1OnePointSubset_eq_erase (4*k+6) Q hQ
  by_cases hxlast : x = Fin.last (4*k+6)
  · left
    simpa only [hxlast] using hx
  · right
    have hlt : x.val < 4*k+6 := by
      have hb := x.isLt
      have hnot : x.val ≠ 4*k+6 := by
        intro he
        apply hxlast
        apply Fin.ext
        simpa only [Fin.val_last] using he
      omega
    let v : Fin (4*k+6) := ⟨x.val, hlt⟩
    refine ⟨v, ?_⟩
    have hxcast : v.castSucc = x := Fin.ext rfl
    simpa only [p1SidePacketOmitOld, hxcast] using hx

/-- The subset of old embedded vertices is the complete side
universe after erasing the last (new) vertex. -/
theorem p1OldBaseImage_univ (k : ℕ) :
    ((Finset.univ : Finset (Fin (4*k+6))).image
      (Fin.castSuccEmb : Fin (4*k+6) ↪ Fin (4*k+6+1))) =
    (Finset.univ : Finset (Fin (4*k+6+1))).erase
      (Fin.last (4*k+6)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hx
    apply Finset.mem_erase.mpr
    constructor
    · intro he
      exact (Fin.castSucc_ne_last v) (hv.trans he)
    · exact Finset.mem_univ _
  · intro hx
    have hxlast : x ≠ Fin.last (4*k+6) :=
      (Finset.mem_erase.mp hx).1
    have hlt : x.val < 4*k+6 := by
      have hb := x.isLt
      have hnot : x.val ≠ 4*k+6 := by
        intro he
        apply hxlast
        apply Fin.ext
        simpa only [Fin.val_last] using he
      omega
    let v : Fin (4*k+6) := ⟨x.val, hlt⟩
    exact Finset.mem_image.mpr
      ⟨v, Finset.mem_univ _, Fin.ext rfl⟩

end Hypertournaments
