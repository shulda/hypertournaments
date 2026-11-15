import Hypertournaments.FiveConstrained.CertificatesBasic
import Hypertournaments.FiveConstrained.CatalogueEncoding
import Hypertournaments.LocalTypes

/-!
# Semantic interpretation of the executable four- and five-packets

Every packet bit is the original intrinsic orientation of an explicitly
increasing tuple. The packet functions also apply to arbitrary vertex carriers
through arbitrary injections; their images need not be increasing in any
ambient vertex order.
-/

namespace Hypertournaments.FiveConstrained

/-- The four increasing triples of four vertices, in lexicographic order. -/
def triple4 (i : Fin 4) : Fin 3 ↪ Fin 4 :=
  tripleEmbedding (![0, 0, 0, 1] i) (![1, 1, 2, 2] i) (![2, 3, 3, 3] i)
    (by
      have h : ∀ j : Fin 4, (![0, 0, 0, 1] j : Fin 4) < ![1, 1, 2, 2] j := by decide
      exact h i)
    (by
      have h : ∀ j : Fin 4, (![1, 1, 2, 2] j : Fin 4) < ![2, 3, 3, 3] j := by decide
      exact h i)

theorem triple4_strictMono (i : Fin 4) :
    StrictMono (triple4 i : Fin 3 → Fin 4) :=
  tripleEmbedding_strictMono _ _ _ _ _

theorem triple5_strictMono (i : Fin 10) :
    StrictMono (triple5 i : Fin 3 → Fin 5) :=
  tripleEmbedding_strictMono _ _ _ _ _

/-- Deletion order and lexicographic triple order run in opposite directions. -/
theorem facet_refl_eq_triple4 (i : Fin 4) :
    facet (Function.Embedding.refl (Fin 4)) i = triple4 (Fin.rev i) := by
  fin_cases i <;> ext j <;> fin_cases j <;> rfl

/-- The finite four-packet checker is exactly the existing intrinsic local
index, with no assumption on the chosen hypertournament. -/
theorem localIndex_eq_certificateType4 (A : Hyper 3 (Fin 4)) :
    localIndex A (Function.Embedding.refl (Fin 4)) =
      certificateType4 (A.orient (triple4 0)) (A.orient (triple4 1))
        (A.orient (triple4 2)) (A.orient (triple4 3)) := by
  have hnorm : (fun i : Fin 4 => normalizedFacet A (Function.Embedding.refl _) i) =
      ![A.orient (triple4 3), !(A.orient (triple4 2)),
        A.orient (triple4 1), !(A.orient (triple4 0))] := by
    funext i
    fin_cases i <;> simp [normalizedFacet, facet_refl_eq_triple4]
  have hcount : ∀ a b c d : Bool,
      ((Finset.univ : Finset (Fin 4)).filter
        (fun i => ![a, b, c, d] i = true)).card =
          a.toNat + b.toNat + c.toNat + d.toNat := by decide
  have hnorm' (i : Fin 4) := congrFun hnorm i
  unfold localIndex positiveFacetCount
  simp_rw [hnorm']
  rw [hcount]
  rfl

/-- The same four-packet formula on an arbitrary intrinsic four-tuple. -/
theorem localIndex_eq_certificateType4_at {V : Type*} (A : Hyper 3 V)
    (e : Fin 4 ↪ V) :
    localIndex A e =
      certificateType4 (A.orient ((triple4 0).trans e))
        (A.orient ((triple4 1).trans e))
        (A.orient ((triple4 2).trans e))
        (A.orient ((triple4 3).trans e)) := by
  exact localIndex_eq_certificateType4 (A.pullback e)

/-- Literal executable ten-bit packet of an actual five-vertex structure. -/
def packet5OfHyper (A : Hyper 3 (Fin 5)) : ℕ :=
  certificatePacket5 (A.orient (triple5 0)) (A.orient (triple5 1))
    (A.orient (triple5 2)) (A.orient (triple5 3))
    (A.orient (triple5 4)) (A.orient (triple5 5))
    (A.orient (triple5 6)) (A.orient (triple5 7))
    (A.orient (triple5 8)) (A.orient (triple5 9))

/-- The certificate's arithmetic packet is the existing intrinsic mask encoder. -/
theorem packet5OfHyper_eq_encode5 (A : Hyper 3 (Fin 5)) :
    packet5OfHyper A = encode5 A := by
  simp only [packet5OfHyper, certificatePacket5, encode5, packBits,
    Fin.isValue, Fin.reduceSucc]
  omega

theorem packet5OfHyper_lt (A : Hyper 3 (Fin 5)) : packet5OfHyper A < 1024 := by
  rw [packet5OfHyper_eq_encode5]
  exact encode5_lt A

/-- Decoding the ten literal packet bits recovers every intrinsic tuple. -/
theorem maskHyper_packet5OfHyper (A : Hyper 3 (Fin 5)) :
    ∀ t, (maskHyper 5 (packet5OfHyper A)).orient t = A.orient t := by
  rw [packet5OfHyper_eq_encode5]
  exact maskHyper_encode5 A

/-- Original arbitrary-coordinate structure embedded into its decoded packet. -/
theorem preserves_packet5OfHyper (A : Hyper 3 (Fin 5)) :
    Preserves A (maskHyper 5 (packet5OfHyper A)) (Function.Embedding.refl _) :=
  maskHyper_packet5OfHyper A

/-- Pulling an arbitrary five-tuple into the literal packet preserves all of
its orientations when the packet is embedded back into the original carrier. -/
theorem packet5OfHyper_preserves_at {V : Type*} (A : Hyper 3 V)
    (e : Fin 5 ↪ V) :
    Preserves (maskHyper 5 (packet5OfHyper (A.pullback e))) A e := by
  intro t
  exact (maskHyper_packet5OfHyper (A.pullback e) t).symm

end Hypertournaments.FiveConstrained
