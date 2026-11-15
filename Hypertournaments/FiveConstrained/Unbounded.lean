import Hypertournaments.FiveConstrained.ClassRecognition
import Hypertournaments.FiveConstrained.Normalization
import Hypertournaments.FiveConstrained.PacketSemantics
import Hypertournaments.FiveConstrained.RamseyHomogeneity

/-!
# Unboundedness of the actual four/five-constrained ternary classes

The necessity direction uses only finite Ramsey in the empty language. The
converse constructs actual constant canonical-sign structures of every size.
The four-condition and the five-condition are retained separately.
-/

namespace Hypertournaments.FiveConstrained

set_option maxHeartbeats 2000000

/-- A constant canonical-sign five-packet has one of the two constant masks. -/
theorem encode5_constant (b : Bool) :
    encode5 (Hyper.fromOrderedSigns (fun _ : Finset (Fin 5) => b)) =
      if b then 1023 else 0 := by
  have hbit (i : Fin 10) :
      (Hyper.fromOrderedSigns (fun _ : Finset (Fin 5) => b)).orient (triple5 i) = b := by
    rw [fromOrderedSigns_orient_strictMono _ _ (triple5_strictMono i)]
  unfold encode5
  simp_rw [hbit]
  cases b <;> decide

theorem type5_constant (b : Bool) :
    type5 (encode5 (Hyper.fromOrderedSigns (fun _ : Finset (Fin 5) => b))) = 0 := by
  rw [encode5_constant]
  cases b <;> decide

/-- Every increasing four-tuple of a constant-sign structure has type `C4`. -/
theorem constant_localIndex {m : ℕ} (b : Bool) (e : Fin 4 ↪ Fin m)
    (he : StrictMono (e : Fin 4 → Fin m)) :
    localIndex (Hyper.fromOrderedSigns (fun _ : Finset (Fin m) => b)) e = 2 := by
  have hbit (i : Fin 4) :
      (Hyper.fromOrderedSigns (fun _ : Finset (Fin m) => b)).orient
        ((triple4 i).trans e) = b := by
    exact fromOrderedSigns_orient_strictMono
      (fun _ : Finset (Fin m) => b) ((triple4 i).trans e)
        (he.comp (triple4_strictMono i))
  rw [localIndex_eq_certificateType4_at]
  simp_rw [hbit]
  cases b <;> decide

/-- Every increasing five-tuple of a constant-sign structure has type `P0`. -/
theorem constant_five_packet_type {m : ℕ} (b : Bool) (e : Fin 5 ↪ Fin m)
    (he : StrictMono (e : Fin 5 → Fin m)) :
    type5 (encode5 ((Hyper.fromOrderedSigns
      (fun _ : Finset (Fin m) => b)).pullback e)) = 0 := by
  have hbit (i : Fin 10) :
      ((Hyper.fromOrderedSigns (fun _ : Finset (Fin m) => b)).pullback e).orient
        (triple5 i) = b := by
    change (Hyper.fromOrderedSigns (fun _ : Finset (Fin m) => b)).orient
      ((triple5 i).trans e) = b
    exact fromOrderedSigns_orient_strictMono
      (fun _ : Finset (Fin m) => b) ((triple5 i).trans e)
        (he.comp (triple5_strictMono i))
  unfold encode5
  simp_rw [hbit]
  cases b <;> decide

theorem constrained_constant {four five m : ℕ}
    (hfour : four.testBit 2 = true) (hfive : five.testBit 0 = true) (b : Bool) :
    Constrained four five (Hyper.fromOrderedSigns (fun _ : Finset (Fin m) => b)) := by
  apply (constrained_iff_increasing four five _).mpr
  constructor
  · intro e he
    rw [constant_localIndex b e he]
    exact hfour
  · intro e he
    apply (packetAllowed_iff_type5 five _).mpr
    rw [constant_five_packet_type b e he]
    exact hfive

/-- The unavoidable five-packet in any unbounded constrained class is `P0`. -/
theorem p0_of_unbounded_constrained {four five : ℕ}
    (hU : (constrainedClass four five).Unbounded) : five.testBit 0 = true := by
  obtain ⟨b, hb⟩ := constant_member_of_unbounded
    (constrainedClass_hereditary four five) hU 5 (by decide)
  have hpacket := hb.2 (Function.Embedding.refl (Fin 5))
  have htype := (packetAllowed_iff_type5 five _).mp hpacket
  have heq : encode5 ((Hyper.fromOrderedSigns
      (fun _ : Finset (Fin 5) => b)).pullback (Function.Embedding.refl (Fin 5))) =
        encode5 (Hyper.fromOrderedSigns (fun _ : Finset (Fin 5) => b)) := by
    apply encode5_congr
    intro t
    rfl
  rw [heq, type5_constant] at htype
  exact htype

/-- The independently prescribed four-palette of an unbounded class admits C4. -/
theorem c4_of_unbounded_constrained {four five : ℕ}
    (hU : (constrainedClass four five).Unbounded) : four.testBit 2 = true := by
  obtain ⟨b, hb⟩ := constant_member_of_unbounded
    (constrainedClass_hereditary four five) hU 4 (by decide)
  have h := hb.1 (Function.Embedding.refl (Fin 4))
  change four.testBit (localIndex
    (Hyper.fromOrderedSigns (fun _ : Finset (Fin 4) => b))
      (Function.Embedding.refl (Fin 4))) = true at h
  rw [constant_localIndex b _ (fun _ _ h => h)] at h
  exact h

/-- Unboundedness requires exactly the two unavoidable local types, even when
the prescribed four- and five-palettes have not yet been normalized. -/
theorem constrainedClass_unbounded_iff (four five : ℕ) :
    (constrainedClass four five).Unbounded ↔
      four.testBit 2 = true ∧ five.testBit 0 = true := by
  constructor
  · intro hU
    exact ⟨c4_of_unbounded_constrained hU, p0_of_unbounded_constrained hU⟩
  · rintro ⟨hfour, hfive⟩ N
    exact ⟨N, le_rfl, Hyper.fromOrderedSigns (fun _ : Finset (Fin N) => false),
      constrained_constant hfour hfive false⟩

/-- In the normalized presentation, membership of `P0` alone is exactly
unboundedness. Impossible higher palette bits do not affect this equivalence. -/
theorem normalizedClass_unbounded_iff (palette : ℕ) :
    (normalizedClass palette).Unbounded ↔ palette.testBit 0 = true := by
  rw [normalizedClass, constrainedClass_unbounded_iff]
  constructor
  · exact And.right
  · intro hP0
    refine ⟨(certificateSupport4_testBit_iff palette 2).mpr ?_, hP0⟩
    exact ⟨0, hP0, by decide⟩

end Hypertournaments.FiveConstrained
