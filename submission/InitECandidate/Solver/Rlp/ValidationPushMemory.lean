import InitECandidate.Solver.Rlp.ValidationRecord

namespace InitECandidate.Solver.Rlp.Validation
open Flapjack PanSemStateFiniteExact
open WitnessRadix

/-- Construct the next physical linked stack from the actual fresh record
writes; every older record is preserved above the old scratch cursor. -/
theorem Pending.after_record (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (rootEnd ending pointer resume : BitVec 64) (frames : List Frame)
    (pending : Pending source.memory source.memaddrs cursor rootEnd frames ending)
    (active : pointer≠0#64) (fits : pointer.toNat+24<2^64) (below : pointer.toNat+24≤cursor)
    (within : resume.toNat≤ending.toNat)
    (mapped0 : source.memaddrs pointer) (mapped8 : source.memaddrs (pointer+8#64)) (mapped16 : source.memaddrs (pointer+16#64)) :
    Pending (recordPost source pointer resume ending (topOf frames)).memory
      (recordPost source pointer resume ending (topOf frames)).memaddrs pointer.toNat rootEnd
      ({pointer:=pointer,resume:=resume,parentEnd:=ending}::frames) resume := by
  have tail := Pending.of_upper_agreement source.memory (WordWrites.write source.memory (recordWrites pointer resume ending (topOf frames)))
    source.memaddrs source.memaddrs cursor pointer.toNat rootEnd frames ending pending rfl (by omega)
    (fun query upper => record_upper_agreement source.memory pointer resume ending (topOf frames) cursor fits below query upper)
  have words := record_words source.memory pointer resume ending (topOf frames) fits
  exact ⟨rfl,active,Nat.le_refl _,fits,within,mapped0,words.1,mapped8,words.2.1,mapped16,words.2.2,tail⟩

end InitECandidate.Solver.Rlp.Validation

#print axioms InitECandidate.Solver.Rlp.Validation.Pending.after_record
