import Hypertournaments.Independent.BasicBridge
import Hypertournaments.PairCancellation
import Hypertournaments.PartialHyper

/-!
# Independent forbidden families and pair cancellation

This module connects the independently supplied definitions to the original
finite omission interface. No theorem about omission classes is assumed here.
-/

namespace IndependentHypertournaments.Bridge

/-- The native family contains exactly the independently forbidden structures.
The inverse representation is unique, so no closure assumption on F is used. -/
def nativeFamily {n : ℕ} (F : FiniteHT n → Prop) :
    Hypertournaments.ForbiddenFamily n :=
  fun m A => F ⟨m, ofHyper A⟩

/-- Omitting the translated family is precisely the independent Forb condition. -/
theorem omits_iff {n m : ℕ} (F : FiniteHT n → Prop)
    (A : Hypertournament n (Fin m)) :
    Hypertournaments.Omits (nativeFamily F) (toHyper A) ↔ Forb F ⟨m, A⟩ := by
  constructor
  · intro h D hD hf
    obtain ⟨f, hf⟩ := hf
    let e : Fin D.1 ↪ Fin m := ⟨f, hf.1⟩
    have hmem : toHyper D.2 ∈ nativeFamily F D.1 := by
      change F ⟨D.1, ofHyper (toHyper D.2)⟩
      simpa only [ofHyper_toHyper] using hD
    exact h D.1 (toHyper D.2) hmem e
      ((embeds_iff_preserves D.2 A e).mp hf)
  · intro h k D hD e he
    change F ⟨k, ofHyper D⟩ at hD
    apply h ⟨k, ofHyper D⟩ hD
    refine ⟨e, (embeds_iff_preserves (ofHyper D) A e).mpr ?_⟩
    simpa only [toHyper_ofHyper] using he

/-- The independent existential first-coordinate condition agrees with the
native universal coordinate condition. The original strict order is retained. -/
theorem increasingLinkTuple_ofLinearOrder_iff {n m : ℕ} (hn : 2 ≤ n)
    (order : LinearOrder (Fin m)) (u v : Fin m) (t : Fin n ↪ Fin m) :
    IncreasingLinkTuple (ofLinearOrder order) u v t ↔
      @Hypertournaments.IsPairLink n (Fin m) order u v t := by
  constructor
  · rintro ⟨_, ⟨i0, i1, hi0, hi1, h0, h1⟩, ht⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      have he : i = i0 := Fin.ext (hi.trans hi0.symm)
      simpa only [he] using h0
    · intro i hi
      have he : i = i1 := Fin.ext (hi.trans hi1.symm)
      simpa only [he] using h1
    · intro i j hi hij
      exact (ofLinearOrder_lt order _ _).mp (ht i j hi hij)
  · intro ht
    refine ⟨t.injective, ?_, ?_⟩
    · refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, rfl, rfl, ?_, ?_⟩
      · exact ht.1 _ rfl
      · exact ht.2.1 _ rfl
    · intro i j hi hij
      exact (ofLinearOrder_lt order _ _).mpr (ht.2.2 i j hi hij)

/-- The same link bridge starts with an independently chosen free order. -/
theorem increasingLinkTuple_toLinearOrder_iff {n m : ℕ} (hn : 2 ≤ n)
    (order : LinearOrderData (Fin m)) (u v : Fin m) (t : Fin n ↪ Fin m) :
    IncreasingLinkTuple order u v t ↔
      @Hypertournaments.IsPairLink n (Fin m) (toLinearOrder order) u v t := by
  constructor
  · rintro ⟨_, ⟨i0, i1, hi0, hi1, h0, h1⟩, ht⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      have he : i = i0 := Fin.ext (hi.trans hi0.symm)
      simpa only [he] using h0
    · intro i hi
      have he : i = i1 := Fin.ext (hi.trans hi1.symm)
      simpa only [he] using h1
    · intro i j hi hij
      exact (toLinearOrder_lt order _ _).mpr (ht i j hi hij)
  · intro ht
    refine ⟨t.injective, ?_, ?_⟩
    · refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, rfl, rfl, ?_, ?_⟩
      · exact ht.1 _ rfl
      · exact ht.2.1 _ rfl
    · intro i j hi hij
      exact (toLinearOrder_lt order _ _).mp (ht.2.2 i j hi hij)

/-- Pair cancellation has exactly the same pair, order, size and link quantifiers
in the two independent orientation representations. -/
theorem pairCancelling_iff {n : ℕ} (A : FiniteHT n) :
    PairCancelling A ↔ Hypertournaments.PairCancelling (toHyper A.2) := by
  constructor
  · rintro ⟨hn, hm, hp⟩
    refine ⟨hn, ?_, ?_⟩
    · simpa only [Nat.card_fin] using hm
    · intro order u v huv
      obtain ⟨f, g, hf, hg, hne⟩ := hp u v huv (ofLinearOrder order)
      let ef : Fin n ↪ Fin A.1 := ⟨f, hf.1⟩
      let eg : Fin n ↪ Fin A.1 := ⟨g, hg.1⟩
      refine ⟨ef, eg,
        (increasingLinkTuple_ofLinearOrder_iff (by omega) order u v ef).mp hf,
        (increasingLinkTuple_ofLinearOrder_iff (by omega) order u v eg).mp hg, ?_⟩
      intro he
      apply hne
      have hz := congrArg Hypertournaments.p1BitToZMod he
      rw [bit_toHyper, bit_toHyper] at hz
      have hef : (ef : Fin n → Fin A.1) = f := by funext i; rfl
      have heg : (eg : Fin n → Fin A.1) = g := by funext i; rfl
      exact (congrArg A.2.orientation hef).symm.trans
        (hz.trans (congrArg A.2.orientation heg))
  · rintro ⟨hn, hm, hp⟩
    refine ⟨hn, ?_, ?_⟩
    · simpa only [Nat.card_fin] using hm
    · intro u v huv order
      obtain ⟨f, g, hf, hg, hne⟩ := hp (toLinearOrder order) u v huv
      refine ⟨f, g,
        (increasingLinkTuple_toLinearOrder_iff (by omega) order u v f).mpr hf,
        (increasingLinkTuple_toLinearOrder_iff (by omega) order u v g).mpr hg, ?_⟩
      intro he
      apply hne
      apply Hypertournaments.p1BitToZMod_injective
      simpa only [bit_toHyper] using he

/-- Translate precisely the original independent forbidden-family hypothesis. -/
theorem nativeFamily_pairCancelling {n : ℕ} (F : FiniteHT n → Prop)
    (hpc : ∀ D, F D → PairCancelling D) :
    ∀ m D, D ∈ nativeFamily F m → Hypertournaments.PairCancelling D := by
  intro m D hD
  have h := (pairCancelling_iff ⟨m, ofHyper D⟩).mp (hpc _ hD)
  simpa only [toHyper_ofHyper] using h

end IndependentHypertournaments.Bridge
