import InitECandidate.Solver.GasBudget.JournalRecordWrites

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix WitnessRadix.QueryBranch MutableTable

/-- The four appended words establish the next actual prefix image. Every
old record remains intact, and the new query is a mapped copied key. -/
theorem record_image {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory) (objects : ι → TableFamily.Object)
    (base cap count cursor : Nat) (entry : Entry ι) (entries : Nat → Entry ι)
    (image : Image source objects base count entries) (zone : Zone objects base cap cursor) (room : count < cap)
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (queryFits : entry.key.toNat + KeyHash.keySize (objects entry.writer).kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize (objects entry.writer).kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress entry.key offset))) :
    Image (recordState source objects base count entry) objects base (count + 1) (Function.update entries count entry) := by
  constructor
  · intro index inside field
    by_cases last : index = count
    · subst index
      exact zone.mapped source domain count room field
    · exact image.mapped index (by omega) field
  · intro index inside field
    by_cases last : index = count
    · subst index
      rw [Function.update_self]
      exact record_word source.memory objects base cap count entry zone.valid room field
    · rw [Function.update_of_ne last]
      exact (record_earlier source.memory objects base cap count index entry zone.valid room (by omega) field).trans (image.words index (by omega) field)
  · intro index inside field table
    exact zone.separate index (by omega) field table
  · intro index inside
    by_cases last : index = count
    · subst index
      rw [Function.update_self]
      exact queryFits
    · rw [Function.update_of_ne last]
      exact image.queryFits index (by omega)
  · intro index inside offset bounded
    by_cases last : index = count
    · subst index
      rw [Function.update_self] at bounded ⊢
      exact queryMapped offset bounded
    · rw [Function.update_of_ne last] at bounded ⊢
      exact image.queryMapped index (by omega) offset bounded

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.record_image
