import Hypertournaments.FiveConstrained.CatalogueEncoding

namespace Hypertournaments.FiveConstrained

/-- Signed pullback of a ten-bit mask by an actual vertex permutation. -/
def relabel5 (m : ℕ) (σ : Equiv.Perm (Fin 5)) : ℕ :=
  encode5 ((maskHyper 5 m).pullback σ.toEmbedding)

theorem relabel5_lt (m : ℕ) (σ : Equiv.Perm (Fin 5)) : relabel5 m σ < 1024 :=
  encode5_lt _

theorem relabel5_orient (m : ℕ) (σ : Equiv.Perm (Fin 5)) (t : Fin 3 ↪ Fin 5) :
    (maskHyper 5 (relabel5 m σ)).orient t =
      (maskHyper 5 m).orient (t.trans σ.toEmbedding) :=
  maskHyper_encode5 _ t

theorem encode5_congr {A B : Hyper 3 (Fin 5)}
    (h : ∀ t, A.orient t = B.orient t) : encode5 A = encode5 B := by
  apply congrArg (packBits 10)
  funext i
  exact h (triple5 i)

theorem relabel5_mul (m : ℕ) (σ τ : Equiv.Perm (Fin 5)) :
    relabel5 (relabel5 m σ) τ = relabel5 m (σ * τ) := by
  apply encode5_congr
  intro t
  change (maskHyper 5 (relabel5 m σ)).orient (t.trans τ.toEmbedding) = _
  rw [relabel5_orient]
  rfl

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem swapChunk0 : ∀ (k : Fin 32) (i : Fin 4),
    type5 (relabel5 (0 + k.val) (Equiv.swap i.castSucc i.succ)) =
      type5 (0 + k.val) := by decide

private theorem swapChunk1 : ∀ (k : Fin 32) (i : Fin 4),
    type5 (relabel5 (32 + k.val) (Equiv.swap i.castSucc i.succ)) =
      type5 (32 + k.val) := by decide

private theorem swapChunk2 : ∀ (k : Fin 32) (i : Fin 4),
    type5 (relabel5 (64 + k.val) (Equiv.swap i.castSucc i.succ)) =
      type5 (64 + k.val) := by decide

private theorem swapChunk3 : ∀ (k : Fin 32) (i : Fin 4),
    type5 (relabel5 (96 + k.val) (Equiv.swap i.castSucc i.succ)) =
      type5 (96 + k.val) := by decide

private theorem swapChunk4 : ∀ (k : Fin 32) (i : Fin 4),
    type5 (relabel5 (128 + k.val) (Equiv.swap i.castSucc i.succ)) =
      type5 (128 + k.val) := by decide

private theorem swapChunk5 : ∀ (k : Fin 32) (i : Fin 4),
    type5 (relabel5 (160 + k.val) (Equiv.swap i.castSucc i.succ)) =
      type5 (160 + k.val) := by decide

private theorem swapChunk6 : ∀ (k : Fin 32) (i : Fin 4),
    type5 (relabel5 (192 + k.val) (Equiv.swap i.castSucc i.succ)) =
      type5 (192 + k.val) := by decide

private theorem swapChunk7 : ∀ (k : Fin 32) (i : Fin 4),
    type5 (relabel5 (224 + k.val) (Equiv.swap i.castSucc i.succ)) =
      type5 (224 + k.val) := by decide

private theorem swapChunk8 : ∀ (k : Fin 32) (i : Fin 4),
    type5 (relabel5 (256 + k.val) (Equiv.swap i.castSucc i.succ)) =
      type5 (256 + k.val) := by decide

private theorem swapChunk9 : ∀ (k : Fin 32) (i : Fin 4),
    type5 (relabel5 (288 + k.val) (Equiv.swap i.castSucc i.succ)) =
      type5 (288 + k.val) := by decide

private theorem swapChunk10 : ∀ (k : Fin 32) (i : Fin 4),
    type5 (relabel5 (320 + k.val) (Equiv.swap i.castSucc i.succ)) =
      type5 (320 + k.val) := by decide

private theorem swapChunk11 : ∀ (k : Fin 32) (i : Fin 4),
    type5 (relabel5 (352 + k.val) (Equiv.swap i.castSucc i.succ)) =
      type5 (352 + k.val) := by decide

private theorem swapChunk12 : ∀ (k : Fin 32) (i : Fin 4),
    type5 (relabel5 (384 + k.val) (Equiv.swap i.castSucc i.succ)) =
      type5 (384 + k.val) := by decide

private theorem swapChunk13 : ∀ (k : Fin 32) (i : Fin 4),
    type5 (relabel5 (416 + k.val) (Equiv.swap i.castSucc i.succ)) =
      type5 (416 + k.val) := by decide

private theorem swapChunk14 : ∀ (k : Fin 32) (i : Fin 4),
    type5 (relabel5 (448 + k.val) (Equiv.swap i.castSucc i.succ)) =
      type5 (448 + k.val) := by decide

private theorem swapChunk15 : ∀ (k : Fin 32) (i : Fin 4),
    type5 (relabel5 (480 + k.val) (Equiv.swap i.castSucc i.succ)) =
      type5 (480 + k.val) := by decide

private theorem swapChunk16 : ∀ (k : Fin 32) (i : Fin 4),
    type5 (relabel5 (512 + k.val) (Equiv.swap i.castSucc i.succ)) =
      type5 (512 + k.val) := by decide

private theorem swapChunk17 : ∀ (k : Fin 32) (i : Fin 4),
    type5 (relabel5 (544 + k.val) (Equiv.swap i.castSucc i.succ)) =
      type5 (544 + k.val) := by decide

private theorem swapChunk18 : ∀ (k : Fin 32) (i : Fin 4),
    type5 (relabel5 (576 + k.val) (Equiv.swap i.castSucc i.succ)) =
      type5 (576 + k.val) := by decide

private theorem swapChunk19 : ∀ (k : Fin 32) (i : Fin 4),
    type5 (relabel5 (608 + k.val) (Equiv.swap i.castSucc i.succ)) =
      type5 (608 + k.val) := by decide

private theorem swapChunk20 : ∀ (k : Fin 32) (i : Fin 4),
    type5 (relabel5 (640 + k.val) (Equiv.swap i.castSucc i.succ)) =
      type5 (640 + k.val) := by decide

private theorem swapChunk21 : ∀ (k : Fin 32) (i : Fin 4),
    type5 (relabel5 (672 + k.val) (Equiv.swap i.castSucc i.succ)) =
      type5 (672 + k.val) := by decide

private theorem swapChunk22 : ∀ (k : Fin 32) (i : Fin 4),
    type5 (relabel5 (704 + k.val) (Equiv.swap i.castSucc i.succ)) =
      type5 (704 + k.val) := by decide

private theorem swapChunk23 : ∀ (k : Fin 32) (i : Fin 4),
    type5 (relabel5 (736 + k.val) (Equiv.swap i.castSucc i.succ)) =
      type5 (736 + k.val) := by decide

private theorem swapChunk24 : ∀ (k : Fin 32) (i : Fin 4),
    type5 (relabel5 (768 + k.val) (Equiv.swap i.castSucc i.succ)) =
      type5 (768 + k.val) := by decide

private theorem swapChunk25 : ∀ (k : Fin 32) (i : Fin 4),
    type5 (relabel5 (800 + k.val) (Equiv.swap i.castSucc i.succ)) =
      type5 (800 + k.val) := by decide

private theorem swapChunk26 : ∀ (k : Fin 32) (i : Fin 4),
    type5 (relabel5 (832 + k.val) (Equiv.swap i.castSucc i.succ)) =
      type5 (832 + k.val) := by decide

private theorem swapChunk27 : ∀ (k : Fin 32) (i : Fin 4),
    type5 (relabel5 (864 + k.val) (Equiv.swap i.castSucc i.succ)) =
      type5 (864 + k.val) := by decide

private theorem swapChunk28 : ∀ (k : Fin 32) (i : Fin 4),
    type5 (relabel5 (896 + k.val) (Equiv.swap i.castSucc i.succ)) =
      type5 (896 + k.val) := by decide

private theorem swapChunk29 : ∀ (k : Fin 32) (i : Fin 4),
    type5 (relabel5 (928 + k.val) (Equiv.swap i.castSucc i.succ)) =
      type5 (928 + k.val) := by decide

private theorem swapChunk30 : ∀ (k : Fin 32) (i : Fin 4),
    type5 (relabel5 (960 + k.val) (Equiv.swap i.castSucc i.succ)) =
      type5 (960 + k.val) := by decide

private theorem swapChunk31 : ∀ (k : Fin 32) (i : Fin 4),
    type5 (relabel5 (992 + k.val) (Equiv.swap i.castSucc i.succ)) =
      type5 (992 + k.val) := by decide

theorem type5_relabel5_adjacent :
    ∀ (m : Fin 1024) (i : Fin 4),
      type5 (relabel5 m.val (Equiv.swap i.castSucc i.succ)) = type5 m.val := by
  intro m i
  have chunks : ∀ (c k : Fin 32) (i : Fin 4),
      type5 (relabel5 (32 * c.val + k.val) (Equiv.swap i.castSucc i.succ)) =
        type5 (32 * c.val + k.val) := by
    intro c
    fin_cases c
    · exact swapChunk0
    · exact swapChunk1
    · exact swapChunk2
    · exact swapChunk3
    · exact swapChunk4
    · exact swapChunk5
    · exact swapChunk6
    · exact swapChunk7
    · exact swapChunk8
    · exact swapChunk9
    · exact swapChunk10
    · exact swapChunk11
    · exact swapChunk12
    · exact swapChunk13
    · exact swapChunk14
    · exact swapChunk15
    · exact swapChunk16
    · exact swapChunk17
    · exact swapChunk18
    · exact swapChunk19
    · exact swapChunk20
    · exact swapChunk21
    · exact swapChunk22
    · exact swapChunk23
    · exact swapChunk24
    · exact swapChunk25
    · exact swapChunk26
    · exact swapChunk27
    · exact swapChunk28
    · exact swapChunk29
    · exact swapChunk30
    · exact swapChunk31
  let c : Fin 32 := ⟨m.val / 32, by omega⟩
  let k : Fin 32 := ⟨m.val % 32, Nat.mod_lt _ (by decide)⟩
  have heq : 32 * c.val + k.val = m.val := by dsimp [c, k]; omega
  simpa only [heq] using chunks c k i

end Hypertournaments.FiveConstrained
