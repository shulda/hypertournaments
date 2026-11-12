import Hypertournaments.OddToggleP3PotentialPresentation
import Hypertournaments.CanonicalPacket

/-!
# Zero facets forced by protected block support of a potential

A potential supported only on finite sets meeting all protected block
labels has zero coboundary on any set missing one protected label.
In particular, if a vertex is the UNIQUE vertex of its protected
block in an (n+1)-packet, deleting it produces a zero orientation
facet of the potential-induced intrinsic hypertournament.

This is a genuine source-support statement, not a probabilistic
claim or a proof that two such vertices of opposite parity always
exist. That remaining finite block geometry is a separate task.
-/

namespace Hypertournaments

/-- Every nonzero potential entry covers every designated block. -/
def p3PotentialCoversBlocks
    {V I : Type*} [DecidableEq V]
    (block : V → I) (protected : Finset I)
    (z : Finset V → ZMod 2) : Prop :=
  ∀ U : Finset V, z U ≠ 0 →
    ∀ i ∈ protected, ∃ v ∈ U, block v = i

/-- Missing an entire protected block forces the coboundary of
any supported potential to vanish on the given finite set. -/
theorem p3Coboundary_zero_of_missing_protected
    {V I : Type*} [DecidableEq V]
    (block : V → I) (protected : Finset I)
    (z : Finset V → ZMod 2)
    (hcover : p3PotentialCoversBlocks block protected z)
    (X : Finset V) (i : I) (hi : i ∈ protected)
    (hmissing : ∀ v ∈ X, block v ≠ i) :
    coboundary z X = 0 := by
  unfold coboundary
  apply Finset.sum_eq_zero
  intro v hv
  by_contra hnonzero
  obtain ⟨w, hw, heq⟩ := hcover (X.erase v) hnonzero i hi
  exact (hmissing w (Finset.mem_of_mem_erase hw)) heq

/-- Deleting the unique vertex of a protected block leaves a
finite set whose potential coboundary is zero. -/
theorem p3Coboundary_zero_of_unique_protected
    {V I : Type*} [DecidableEq V]
    (block : V → I) (protected : Finset I)
    (z : Finset V → ZMod 2)
    (hcover : p3PotentialCoversBlocks block protected z)
    (X : Finset V) (v : V)
    (hprotected : block v ∈ protected)
    (hunique : ∀ w ∈ X, block w = block v → w = v) :
    coboundary z (X.erase v) = 0 := by
  apply p3Coboundary_zero_of_missing_protected
    block protected z hcover (X.erase v)
    (block v) hprotected
  intro w hw heq
  have hwne : w ≠ v := (Finset.mem_erase.mp hw).1
  exact hwne (hunique w (Finset.mem_of_mem_erase hw) heq)

/-- The deleted facet's actual Boolean potential sign is zero. -/
theorem p3PotentialSign_zero_of_unique_protected
    {a : ℕ} {I : Type*}
    (block : Fin a → I) (protected : Finset I)
    (z : Finset (Fin a) → ZMod 2)
    (hcover : p3PotentialCoversBlocks block protected z)
    (X : Finset (Fin a)) (v : Fin a)
    (hprotected : block v ∈ protected)
    (hunique : ∀ w ∈ X, block w = block v → w = v) :
    p3PotentialSign z (X.erase v) = false := by
  have hz := p3Coboundary_zero_of_unique_protected
    block protected z hcover X v hprotected hunique
  simp [p3PotentialSign, p3ZMod2ToBool, hz]

/-- The preceding finite-set source-support lemma applies to
a genuine increasing hypertournament packet: unique block on the
packet guarantees a zero canonical sign after deleting that vertex. -/
theorem p3PotentialSign_zero_on_unique_packet_block
    {n a : ℕ} {I : Type*}
    (block : Fin a → I) (protected : Finset I)
    (z : Finset (Fin a) → ZMod 2)
    (hcover : p3PotentialCoversBlocks block protected z)
    (f : Fin (n+1) ↪o Fin a) (i : Fin (n+1))
    (hprotected : block (f i) ∈ protected)
    (hunique : ∀ j : Fin (n+1),
      block (f j) = block (f i) → j = i) :
    p3PotentialSign z
      (tupleVertices (facet f.toEmbedding i)) = false := by
  have hu : ∀ w ∈ tupleVertices f.toEmbedding,
      block w = block (f i) → w = f i := by
    intro w hw heq
    change w ∈ Finset.univ.image f.toEmbedding at hw
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw
    exact congrArg (fun j => f j) (hunique j heq)
  have hz := p3PotentialSign_zero_of_unique_protected
    block protected z hcover (tupleVertices f.toEmbedding)
    (f i) hprotected hu
  rw [tupleVertices_facet_eq_erase f.toEmbedding i]
  exact hz

end Hypertournaments
