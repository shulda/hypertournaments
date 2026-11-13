import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Hypertournaments.OddToggleP3FreshPacketOrder

/-!
# Old-part order enumeration of a canonical one-fresh packet

An increasing (n+1)-packet in Fin(a+1) containing Fin.last a has
its fresh vertex in the last position. Its first n positions,
viewed in Fin a, form an increasing embedding and consequently
are exactly the canonical increasing enumeration of their old
vertex set U. In particular, U has n vertices and their
deletion-position parities agree with those in the original
fresh-containing packet.

This is an exact finite order argument, not an expansion of
the hypertournament language. It does not claim age membership.
-/

namespace Hypertournaments

/-- Every fresh-containing increasing packet has an old subset
whose canonical increasing enumeration agrees exactly with
all the packet positions before its final fresh vertex. -/
theorem p3CanonicalFresh_old_enumeration
    (a n : ℕ) (f : Fin (n+1) ↪o Fin (a+1))
    (hFresh : Fin.last a ∈ tupleVertices f.toEmbedding) :
    ∃ (U : Finset (Fin a)) (hU : U.card = n),
      ∀ i : Fin n,
        (U.orderEmbOfFin hU i).castSucc = f i.castSucc := by
  classical
  let old : Fin n → Fin a := fun i =>
    ⟨(f i.castSucc).val, by
      have hne := p3CanonicalPacket_old_position_ne_fresh
        a n f hFresh i
      have hbound : (f i.castSucc).val < a+1 :=
        (f i.castSucc).isLt
      have hneq : (f i.castSucc).val ≠ a := by
        intro heq
        apply hne
        apply Fin.ext
        exact heq
      omega⟩
  have hStrict : StrictMono old := by
    intro i j hij
    have hij' : i.castSucc < j.castSucc := by
      apply Fin.lt_def.mpr
      exact Fin.lt_def.mp hij
    have hf : f i.castSucc < f j.castSucc :=
      f.strictMono hij'
    exact Fin.lt_def.mpr (Fin.lt_def.mp hf)
  let e : Fin n ↪o Fin a :=
    OrderEmbedding.ofStrictMono old hStrict
  let U : Finset (Fin a) := Finset.univ.image e
  have hU : U.card = n := by
    dsimp [U]
    rw [Finset.card_image_of_injective _ e.injective]
    simp
  have hMember : ∀ i : Fin n, e i ∈ U := by
    intro i
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hUnique :
      (fun i : Fin n => e i) =
        (U.orderEmbOfFin hU : Fin n → Fin a) :=
    Finset.orderEmbOfFin_unique hU hMember e.strictMono
  refine ⟨U, hU, ?_⟩
  intro i
  have hEq : e i = U.orderEmbOfFin hU i := congrFun hUnique i
  rw [← hEq]
  apply Fin.ext
  rfl

end Hypertournaments
