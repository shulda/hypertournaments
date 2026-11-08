import Hypertournaments.SeedFourData

/-!
# Direct subset-rank certificate for the arity-four seed

For Q of size five, the canonical normalized sign of the facet
Q\\{v} is the unordered orientation sign toggled exactly when
the number of vertices in Q below v is odd. The computation below
uses only finite sets and cardinalities. Its equivalence with
`localIndex` will be proved in a separate general lemma.
-/

namespace Hypertournaments

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Number of positive normalized facets, read from a finite-set
sign table by using the rank of each omitted vertex. -/
def directFacetPositiveCount {k : ℕ}
    (signs : Finset (Fin k) → Bool) (Q : Finset (Fin k)) : ℕ :=
  (Q.filter (fun v =>
    Bool.xor (signs (Q.erase v))
      (decide ((Q.filter (· < v)).card % 2 = 1)) = true)).card

def directCentral4At {k : ℕ}
    (signs : Finset (Fin k) → Bool) (Q : Finset (Fin k)) : Prop :=
  Q.card = 5 →
    min (directFacetPositiveCount signs Q)
        (5 - directFacetPositiveCount signs Q) = 2

/-- The exact seven-vertex source table has central normalized
packet on every five-subset. -/
theorem seed4_base_directCentral :
    ∀ Q : Finset (Fin 7), directCentral4At seed4BaseSigns Q := by
  unfold directCentral4At directFacetPositiveCount
  decide +kernel

end Hypertournaments
