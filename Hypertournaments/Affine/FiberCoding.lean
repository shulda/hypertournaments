import Hypertournaments.Affine.Data
import Hypertournaments.Affine.OrderedLabels
import Mathlib.Tactic.SplitIfs

/-!
# Free oriented codes for affine palette fibers

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
"Further potential constructions". The auxiliary palette is freely paired,
even when the original palette has fixed points. Decoding is equivariant
on all injective tuples and is independent of the chosen vertex order.
-/

universe u v w z

namespace Hypertournaments.Affine

variable {Q : Type u} {G : Type v} [AddCommGroup G]

/-- A surjective parametrization of the fiber over `g`, with domain `Q`.
An element outside that fiber is replaced by one chosen element of it. -/
noncomputable def Data.fiberLabel (d : Data Q G) (g : G) (k : Q) : Q := by
  classical
  exact if d.effective k = g then k else Classical.choose (d.onto g)

@[simp] theorem Data.fiberLabel_effective (d : Data Q G) (g : G) (k : Q) :
    d.effective (d.fiberLabel g k) = g := by
  classical
  unfold Data.fiberLabel
  split_ifs with h
  · exact h
  · exact Classical.choose_spec (d.onto g)

@[simp] theorem Data.fiberLabel_eq (d : Data Q G) {g : G} {q : Q}
    (h : d.effective q = g) : d.fiberLabel g q = q := by
  classical
  simp [Data.fiberLabel, h]

/-- Decode a free oriented code inside a prescribed effective fiber. -/
noncomputable def Data.decode (d : Data Q G) (g : G) (code : Q × Bool) : Q :=
  if code.2 then d.palette.star (d.fiberLabel (d.offset - g) code.1)
    else d.fiberLabel g code.1

@[simp] theorem Data.decode_effective (d : Data Q G) (g : G) (code : Q × Bool) :
    d.effective (d.decode g code) = g := by
  rcases code with ⟨k, b⟩
  cases b <;> simp [Data.decode, d.map_star, sub_sub_cancel]

/-- Reversing the tuple reverses its free code and applies the actual palette
involution, including at fixed labels and when fiber codes repeat. -/
theorem Data.decode_star (d : Data Q G) (g : G) (code : Q × Bool) :
    d.decode (d.offset - g) ((Palette.free Q).star code) =
      d.palette.star (d.decode g code) := by
  rcases code with ⟨k, b⟩
  cases b <;> simp [Data.decode, sub_sub_cancel]

/-- The false sheet supplies a section of the decoder on every effective fiber. -/
@[simp] theorem Data.decode_section (d : Data Q G) (q : Q) :
    d.decode (d.effective q) (q, false) = q := by
  simp [Data.decode]

theorem Data.decode_surjective_fiber (d : Data Q G) (g : G) (q : Q)
    (hq : d.effective q = g) : ∃ code : Q × Bool, d.decode g code = q := by
  refine ⟨(q, false), ?_⟩
  simpa only [hq] using d.decode_section q

/-- Applying the effective map retains the affine permutation law. -/
def Data.effectiveLabelled (d : Data Q G) {n : ℕ} {V : Type w}
    (raw : Labelled n d.palette V) : Labelled n (Palette.affine d.offset) V where
  label t := d.effective (raw.label t)
  swap_label t i j hij := by
    change d.effective (raw.label _) = d.offset - d.effective (raw.label t)
    rw [raw.swap_label t i j hij]
    exact d.map_star _

/-- Decode two intrinsic label structures, without using a vertex order. -/
noncomputable def Data.decodeLabelled (d : Data Q G) {n : ℕ} {V : Type w}
    (effective : Labelled n (Palette.affine d.offset) V)
    (code : Labelled n (Palette.free Q) V) : Labelled n d.palette V where
  label t := d.decode (effective.label t) (code.label t)
  swap_label t i j hij := by
    rw [effective.swap_label t i j hij, code.swap_label t i j hij]
    exact d.decode_star _ _

@[simp] theorem Data.decodeLabelled_effective (d : Data Q G) {n : ℕ} {V : Type w}
    (effective : Labelled n (Palette.affine d.offset) V)
    (code : Labelled n (Palette.free Q) V) (t : Fin n ↪ V) :
    d.effective ((d.decodeLabelled effective code).label t) = effective.label t :=
  d.decode_effective _ _

/-- Preserving potential-effective labels and the fixed code preserves every
actual raw label, independently of any orders on either carrier. -/
theorem Data.decodeLabelled_preserves (d : Data Q G) {n : ℕ}
    {V : Type w} {W : Type z}
    {effectiveV : Labelled n (Palette.affine d.offset) V}
    {effectiveW : Labelled n (Palette.affine d.offset) W}
    {codeV : Labelled n (Palette.free Q) V} {codeW : Labelled n (Palette.free Q) W}
    (e : V ↪ W) (he : effectiveV.Preserves effectiveW e)
    (hc : codeV.Preserves codeW e) :
    (d.decodeLabelled effectiveV codeV).Preserves (d.decodeLabelled effectiveW codeW) e := by
  intro t
  change d.decode (effectiveW.label (t.trans e)) (codeW.label (t.trans e)) =
    d.decode (effectiveV.label t) (codeV.label t)
  rw [he t, hc t]

/-- If effective labels are unchanged, the same intrinsic code decodes the
same raw structure. The conclusion holds before any linear order is chosen. -/
theorem Data.decodeLabelled_congr_effective (d : Data Q G) {n : ℕ} {V : Type w}
    (effective effective' : Labelled n (Palette.affine d.offset) V)
    (code : Labelled n (Palette.free Q) V)
    (h : ∀ t, effective'.label t = effective.label t) :
    d.decodeLabelled effective' code = d.decodeLabelled effective code := by
  apply Labelled.ext
  intro t
  change d.decode (effective'.label t) (code.label t) =
    d.decode (effective.label t) (code.label t)
  rw [h t]

/-- One fixed oriented code for a given ordered raw structure. On increasing
canonical tuples the code uses its false sheet; other tuples follow the free
involution. No finiteness assumption on the carrier is needed. -/
noncomputable def Data.encode {n : ℕ} {V : Type w} [LinearOrder V]
    (d : Data Q G) (raw : Labelled n d.palette V) : Labelled n (Palette.free Q) V :=
  Labelled.fromOrderedLabels (Palette.free Q)
    (fun S => (raw.canonicalTable (Classical.choose (d.onto 0)) S, false))

theorem Data.encode_label_strictMono {n : ℕ} {V : Type w} [LinearOrder V]
    (d : Data Q G) (raw : Labelled n d.palette V) (t : Fin n ↪ V)
    (ht : StrictMono (t : Fin n → V)) :
    (d.encode raw).label t = (raw.label t, false) := by
  have hraw := raw.from_canonicalTable_label (Classical.choose (d.onto 0)) t
  rw [fromOrderedLabels_label_strictMono _ _ t ht] at hraw
  change (Labelled.fromOrderedLabels (Palette.free Q) _).label t = _
  rw [fromOrderedLabels_label_strictMono _ _ t ht, hraw]

/-- The ordered section reconstructs the original intrinsic raw structure on
all tuples, not only the increasing representatives. -/
theorem Data.decode_encode {n : ℕ} {V : Type w} [LinearOrder V]
    (d : Data Q G) (raw : Labelled n d.palette V) :
    d.decodeLabelled (d.effectiveLabelled raw) (d.encode raw) = raw := by
  apply Labelled.ext
  apply Labelled.labels_equal_of_canonical _ raw
  intro S hS
  change d.decode (d.effective (raw.label (S.orderEmbOfFin hS).toEmbedding))
    ((d.encode raw).label (S.orderEmbOfFin hS).toEmbedding) = _
  rw [d.encode_label_strictMono raw _ (S.orderEmbOfFin hS).strictMono]
  exact d.decode_section _

/-- Ordered raw embeddings preserve the chosen intrinsic code. This is only
used to transport original source copies into the independent code language. -/
theorem Data.encode_preserves {n : ℕ} {V : Type w} {W : Type z}
    [LinearOrder V] [LinearOrder W] (d : Data Q G)
    (A : Labelled n d.palette V) (B : Labelled n d.palette W)
    (e : V ↪o W) (he : A.Preserves B e.toEmbedding) :
    (d.encode A).Preserves (d.encode B) e.toEmbedding := by
  apply Labelled.preserves_of_canonical
  intro S hS
  rw [d.encode_label_strictMono B _ (e.strictMono.comp (S.orderEmbOfFin hS).strictMono),
    d.encode_label_strictMono A _ (S.orderEmbOfFin hS).strictMono]
  exact congrArg (fun q => (q, false)) (he (S.orderEmbOfFin hS).toEmbedding)

end Hypertournaments.Affine
