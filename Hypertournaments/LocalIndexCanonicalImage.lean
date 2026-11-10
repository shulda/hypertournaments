import Hypertournaments.OnePointNonmixedAdmissible
import Hypertournaments.CanonicalPacket

/-!
# Intrinsic local indices on increasing images of finite packets

An increasing vertex embedding preserving an intrinsic hypertournament
takes the unique increasing enumeration of a finite (n+1)-subset to
the unique increasing enumeration of its image. Consequently its
local index is unchanged, including the two canonical one-point
joint inclusions used in the exceptional p1 obstruction.

There is no extra order in the hypertournament language: the order
on Fin indexes only serves to pick canonical tuples.
-/

namespace Hypertournaments

theorem localIndex_image_orderEmb_preserves
    {n a b : ℕ}
    (A : Hyper n (Fin a)) (B : Hyper n (Fin b))
    (e : Fin a ↪o Fin b)
    (he : Preserves A B e.toEmbedding)
    (Q : Finset (Fin a)) (hQ : Q.card = n+1) :
    localIndex B
      (((Q.image e).orderEmbOfFin
        (by
          rw [Finset.card_image_of_injective _ e.injective]
          exact hQ)).toEmbedding) =
    localIndex A (Q.orderEmbOfFin hQ).toEmbedding := by
  have him : (Q.image e).card = n+1 := by
    rw [Finset.card_image_of_injective _ e.injective]
    exact hQ
  have hsource : ∀ i : Fin (n+1), (Q.orderEmbOfFin hQ i) ∈ Q := by
    intro i
    have hv : Q.orderEmbOfFin hQ i ∈
        (Finset.univ : Finset (Fin (n+1))).image (Q.orderEmbOfFin hQ) :=
      Finset.mem_image_of_mem _ (Finset.mem_univ i)
    rw [Finset.image_orderEmbOfFin_univ Q hQ] at hv
    exact hv
  have hmem : ∀ i : Fin (n+1),
      e (Q.orderEmbOfFin hQ i) ∈ Q.image e := by
    intro i
    exact Finset.mem_image_of_mem e (hsource i)
  have hmono :
      StrictMono (fun i : Fin (n+1) => e (Q.orderEmbOfFin hQ i)) :=
    e.strictMono.comp (Q.orderEmbOfFin hQ).strictMono
  have hsorted :
      (fun i : Fin (n+1) => e (Q.orderEmbOfFin hQ i)) =
        ((Q.image e).orderEmbOfFin him : Fin (n+1) → Fin b) :=
    Finset.orderEmbOfFin_unique him hmem hmono
  have htuple :
      (Q.orderEmbOfFin hQ).toEmbedding.trans e.toEmbedding =
        ((Q.image e).orderEmbOfFin him).toEmbedding := by
    ext i
    exact congrArg Fin.val (congrFun hsorted i)
  have hlocal := localIndex_preserves A B e.toEmbedding he
    (Q.orderEmbOfFin hQ).toEmbedding
  rw [htuple] at hlocal
  simpa using hlocal.symm

end Hypertournaments
