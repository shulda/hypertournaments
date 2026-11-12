import Hypertournaments.OddToggleP3SixRepeatGlobalSingletons

/-!
# Counting repeated adjacent block labels from the image cardinality

A word on N positions with at least N-2 distinct values can have
at most two equal-adjacent edges among its first six positions.
This does NOT require monotonicity: deleting the successors of
any equal-adjacent edges preserves the set of attained values,
because each value has a least occurrence and that occurrence
can never be a selected equal-edge successor.

The proof uses the exact finite image of the word, not a
heuristic identification of duplicated blocks with repeated edges.
Together with the existing six-edge selector it yields genuine
opposite-parity globally singleton block labels whenever the word
has at least N-2 distinct labels.
-/

namespace Hypertournaments

/-- A word with at least N-2 distinct values can repeat on at
most two of its first six consecutive edges. Monotonicity is
not assumed; a repeated successor is never the first occurrence
of its label. -/
theorem p3SixRepeat_le_two_of_image_card
    {N : ℕ} (hN : 7 ≤ N) (block : Fin N → ℕ)
    (hImageLarge :
      N-2 ≤ ((Finset.univ : Finset (Fin N)).image block).card) :
    (Finset.univ.filter
      (fun i : Fin 6 => p3SixActualRepeatFlags hN block i = true)).card ≤ 2 := by
  classical
  let bad : Finset (Fin 6) :=
    Finset.univ.filter
      (fun i : Fin 6 => p3SixActualRepeatFlags hN block i = true)
  let removed : Finset (Fin N) := bad.image (p3SixSuccessor N hN)
  have hSuccInj : Function.Injective (p3SixSuccessor N hN) := by
    intro i j hij
    apply Fin.ext
    have hv := congrArg Fin.val hij
    change i.val+1 = j.val+1 at hv
    omega
  have hRemovedCard : removed.card = bad.card :=
    Finset.card_image_of_injective bad hSuccInj
  let kept : Finset (Fin N) := Finset.univ \ removed
  have hPreserved :
      kept.image block =
        (Finset.univ : Finset (Fin N)).image block := by
    apply Finset.Subset.antisymm
    · intro v hv
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    · intro v hv
      obtain ⟨j, _, hval⟩ := Finset.mem_image.mp hv
      let fiber : Finset (Fin N) :=
        Finset.univ.filter (fun z => block z = v)
      have hf : fiber.Nonempty := by
        refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        exact hval
      let first : Fin N := fiber.min' hf
      have hfirst : block first = v :=
        (Finset.mem_filter.mp (Finset.min'_mem fiber hf)).2
      have hNotRemoved : first ∉ removed := by
        intro hmem
        obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hmem
        have hbad : p3SixActualRepeatFlags hN block i = true :=
          (Finset.mem_filter.mp hi).2
        have hSame :
            block (p3SixPosition N hN i) =
              block (p3SixSuccessor N hN i) := by
          simpa [p3SixActualRepeatFlags] using hbad
        have hPrevMem : p3SixPosition N hN i ∈ fiber := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          calc
            block (p3SixPosition N hN i) =
                block (p3SixSuccessor N hN i) := hSame
            _ = block first := congrArg block heq
            _ = v := hfirst
        have hle : first ≤ p3SixPosition N hN i :=
          Finset.min'_le fiber _ hPrevMem
        have hlt : p3SixPosition N hN i < first := by
          rw [← heq]
          apply Fin.lt_def.mpr
          change i.val < i.val+1
          omega
        exact (not_lt_of_ge hle) hlt
      exact Finset.mem_image.mpr
        ⟨first,
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hNotRemoved⟩,
          hfirst⟩
  have hImageBound :
      ((Finset.univ : Finset (Fin N)).image block).card ≤
        kept.card := by
    rw [← hPreserved]
    exact Finset.card_image_le
  have hCardSum : kept.card + removed.card = N := by
    simpa [kept] using
      (Finset.card_sdiff_add_card_eq_card
        (Finset.subset_univ removed))
  have hBad : bad.card ≤ 2 := by omega
  exact hBad

/-- The already certified six-edge parity selector applies whenever
a monotone block-word has at least N-2 attained labels. -/
theorem p3SixDistinctLabels_oppositeParity_singletons
    {N : ℕ} (hN : 7 ≤ N) (block : Fin N → ℕ)
    (hMono : Monotone block)
    (hImageLarge :
      N-2 ≤ ((Finset.univ : Finset (Fin N)).image block).card) :
    ∃ x y : Fin N,
      x.val%2=0 ∧ y.val%2=1 ∧
      (∀ z : Fin N, block z = block x → z=x) ∧
      (∀ z : Fin N, block z = block y → z=y) := by
  exact p3SixRepeat_global_oppositeParity_singletons
    hN block hMono
    (p3SixRepeat_le_two_of_image_card hN block hImageLarge)

end Hypertournaments
