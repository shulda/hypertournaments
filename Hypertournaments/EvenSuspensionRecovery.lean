import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Hypertournaments.EvenSuspensionSigns
import Hypertournaments.CanonicalOrientationRecovery

/-!
# Exact source orientation recovery for the even suspension

The lifted (n+2)-hypertournament is defined by a concrete ordered
sign table. The tuple with two increasing pads and a canonical
increasing old n-tuple is itself strictly increasing; its vertex set
is exactly the two-pad packet already handled by the sign table.

The arbitrary-order recovery theorem then follows from the
all-arity canonical-orientation certificate. The entire argument
uses the intrinsic orientation law and no order on an eventual
ordinary amalgam.
-/

namespace Hypertournaments

/-- A padded vertex is never in the range of the old-vertex injection. -/
theorem evenPadShift_not_mem_old (m k : ℕ) (x : Fin m) :
    evenPadShift m k x ∉ Set.range (evenOldShift m k) := by
  rintro ⟨u, hu⟩
  exact evenPadShift_ne_oldShift m k x u hu.symm

/-- The actual intrinsic two-pad tuple of two different pads and an
old n-tuple, in the fixed increasing auxiliary vertex order. -/
def evenPaddedTuple
    {n : ℕ} (m k : ℕ) (x y : Fin m) (hxy : x < y)
    (t : Fin n ↪ Fin k) : Fin (n + 2) ↪ Fin (m + k) :=
  twoPadSliceTuple (evenOldShift m k)
    (evenPadShift m k x) (evenPadShift m k y)
    (evenPadShift_not_mem_old m k x)
    (evenPadShift_not_mem_old m k y)
    (fun he => (ne_of_lt hxy) ((evenPadShift m k).injective he)) t

/-- The finite vertex set of an actual padded tuple is the set
consisting of its two pads together with the images of its old
vertices. This lemma holds for arbitrary (not necessarily monotone)
old injective tuples. -/
theorem evenPaddedTuple_vertices
    {n : ℕ} (m k : ℕ) (x y : Fin m) (hxy : x < y)
    (t : Fin n ↪ Fin k) :
    tupleVertices (evenPaddedTuple m k x y hxy t) =
      evenPaddedPacket m k x y (tupleVertices t) := by
  classical
  ext v
  simp only [tupleVertices, Finset.mem_image, Finset.mem_univ,
    true_and, evenPaddedPacket, Finset.mem_insert]
  constructor
  · rintro ⟨i, hi⟩
    revert hi
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun z => ?_) j) i
    · intro hi
      left
      simpa [evenPaddedTuple, twoPadSliceTuple] using hi.symm
    · intro hi
      right
      left
      simpa [evenPaddedTuple, twoPadSliceTuple] using hi.symm
    · intro hi
      right
      right
      refine ⟨t z, ⟨z, rfl⟩, ?_⟩
      simpa [evenPaddedTuple, twoPadSliceTuple] using hi
  · rintro (hx | hy | ⟨u, ⟨z, hz⟩, hzu⟩)
    · refine ⟨0, ?_⟩
      simpa [evenPaddedTuple, twoPadSliceTuple] using hx.symm
    · refine ⟨1, ?_⟩
      simpa [evenPaddedTuple, twoPadSliceTuple] using hy.symm
    · refine ⟨z.succ.succ, ?_⟩
      calc
        evenPaddedTuple m k x y hxy t z.succ.succ =
            evenOldShift m k (t z) := by
          simp [evenPaddedTuple, twoPadSliceTuple]
        _ = evenOldShift m k u := congrArg (evenOldShift m k) hz
        _ = v := hzu

/-- A canonical old increasing tuple, preceded by ordered pads x<y,
is also an increasing tuple of the entire padded vertex set. -/
theorem evenPaddedTuple_strictMono
    {n : ℕ} (m k : ℕ) (x y : Fin m) (hxy : x < y)
    (t : Fin n ↪o Fin k) :
    StrictMono
      (evenPaddedTuple m k x y hxy t.toEmbedding :
        Fin (n + 2) → Fin (m + k)) := by
  let tail : Fin n → Fin (m + k) :=
    fun i => evenOldShift m k (t i)
  have htail : StrictMono tail := by
    intro i j hij
    change m + (t i).val < m + (t j).val
    have hh : (t i).val < (t j).val := t.strictMono hij
    omega
  have hyOld (i : Fin n) : evenPadShift m k y < tail i := by
    change y.val < m + (t i).val
    omega
  have hxy' : evenPadShift m k x < evenPadShift m k y := by
    change x.val < y.val
    exact hxy
  have hxAll : ∀ i : Fin (n + 1),
      evenPadShift m k x <
        ((Fin.cons (evenPadShift m k y) tail) :
          Fin (n + 1) → Fin (m + k)) i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hxy'
    · exact lt_trans hxy' (hyOld j)
  have hmono :
      StrictMono (Fin.cons (evenPadShift m k x)
        (Fin.cons (evenPadShift m k y) tail)) :=
    (Fin.strictMono_cons).2
      ⟨hxAll, (Fin.strictMono_cons).2 ⟨hyOld, htail⟩⟩
  have heq :
      (fun i : Fin (n + 2) =>
        evenPaddedTuple m k x y hxy t.toEmbedding i) =
      Fin.cons (evenPadShift m k x)
        (Fin.cons (evenPadShift m k y) tail) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun z => ?_) j) i
    · simp [evenPaddedTuple, twoPadSliceTuple]
    · simp [evenPaddedTuple, twoPadSliceTuple]
    · simp [evenPaddedTuple, twoPadSliceTuple, tail]
  change StrictMono (fun i : Fin (n + 2) =>
    evenPaddedTuple m k x y hxy t.toEmbedding i)
  rw [heq]
  exact hmono

/-- On two increasing pads and an increasing old n-tuple, the
intrinsic lifted orientation equals the original n-orientation. -/
theorem evenSuspension_orient_increasing_twoPads
    {n : ℕ} (m k : ℕ) (A : Hyper n (Fin k))
    (x y : Fin m) (hxy : x < y)
    (t : Fin n ↪o Fin k) :
    (A.evenSuspension m k).orient
      (evenPaddedTuple m k x y hxy t.toEmbedding) =
      A.orient t.toEmbedding := by
  let f : Fin (n + 2) ↪ Fin (m + k) :=
    evenPaddedTuple m k x y hxy t.toEmbedding
  have hmono : StrictMono (f : Fin (n + 2) → Fin (m + k)) :=
    evenPaddedTuple_strictMono m k x y hxy t
  have hsource :
      A.canonicalSignTable (tupleVertices t.toEmbedding) =
        A.orient t.toEmbedding := by
    calc
      A.canonicalSignTable (tupleVertices t.toEmbedding) =
          (Hyper.fromOrderedSigns A.canonicalSignTable).orient
            t.toEmbedding :=
        (fromOrderedSigns_orient_strictMono
          A.canonicalSignTable t.toEmbedding t.strictMono).symm
      _ = A.orient t.toEmbedding :=
        A.from_canonicalSignTable_orient t.toEmbedding
  calc
    (A.evenSuspension m k).orient f =
        evenSuspensionSignTable m k A (tupleVertices f) :=
      fromOrderedSigns_orient_strictMono
        (evenSuspensionSignTable m k A) f hmono
    _ = evenSuspensionSignTable m k A
          (evenPaddedPacket m k x y (tupleVertices t.toEmbedding)) := by
      rw [evenPaddedTuple_vertices]
    _ = A.canonicalSignTable (tupleVertices t.toEmbedding) :=
      evenSuspensionSignTable_twoPads m k A x y _ (ne_of_lt hxy)
    _ = A.orient t.toEmbedding := hsource

/-- Exact old orientation recovery for ALL ordered injective old
n-tuples. The proof relies on canonical source recovery, not a new
order or a case enumeration over old vertex permutations. -/
theorem evenSuspension_orient_twoPads
    {n : ℕ} (m k : ℕ) (A : Hyper n (Fin k))
    (x y : Fin m) (hxy : x < y)
    (t : Fin n ↪ Fin k) :
    (A.evenSuspension m k).orient
      (evenPaddedTuple m k x y hxy t) = A.orient t := by
  have hc :
      ∀ (Q : Finset (Fin k)) (hQ : Q.card = n),
        (A.evenSuspension m k).orient
          (evenPaddedTuple m k x y hxy
            (Q.orderEmbOfFin hQ).toEmbedding) =
          A.orient (Q.orderEmbOfFin hQ).toEmbedding := by
    intro Q hQ
    exact evenSuspension_orient_increasing_twoPads
      m k A x y hxy (Q.orderEmbOfFin hQ)
  exact twoPad_source_recovery_of_canonical
    A (A.evenSuspension m k) (evenOldShift m k)
    (evenPadShift m k x) (evenPadShift m k y)
    (evenPadShift_not_mem_old m k x)
    (evenPadShift_not_mem_old m k y)
    (fun he => (ne_of_lt hxy) ((evenPadShift m k).injective he))
    hc t

end Hypertournaments
