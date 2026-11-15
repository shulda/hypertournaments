import Hypertournaments.FiveConstrained.Classes
import Hypertournaments.FiveConstrained.CatalogueIsomorphism

namespace Hypertournaments.FiveConstrained

/-- The executable catalogue recognizes the actual intrinsic packet predicate. -/
theorem packetAllowed_iff_type5 (palette : ℕ) (A : Hyper 3 (Fin 5)) :
    PacketAllowed palette A ↔ palette.testBit (type5 (encode5 A)).val = true := by
  constructor
  · rintro ⟨t, ht, hIso⟩
    have heq := (representative_iso_iff_type5 A t).mp hIso
    simpa only [heq] using ht
  · intro h
    exact ⟨type5 (encode5 A), h, (representative_iso_iff_type5 A _).mpr rfl⟩

end Hypertournaments.FiveConstrained
