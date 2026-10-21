import InitECandidate.Solver.Mpt.WitnessRecordArena
import InitECandidate.Solver.Mpt.LocalFieldStores

namespace InitECandidate.Solver.Mpt.WitnessRecord
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Any fields physically inside the actual new record preserve all older
active scratch records and persistent storage above the incoming cursor. -/
theorem writes_above (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor limit : BitVec 64)
    (arena : Rlp.Validation.Arena source cursor limit) (room : Arenas.Room .down cursor limit 88#64)
    (fields : List LocalFields.Field) (inside : ∀ field∈fields,field.offset<88)
    (memory : WordWrites.Memory) (query : BitVec 64) (above : cursor.toNat≤query.toNat) :
    WordWrites.write memory (LocalFields.writes (pointer cursor) fields) query=memory query := by
  obtain ⟨buffer,lower,upper,aligned,nonzero⟩:=allocation_bounds source cursor limit arena room
  let region : MutableTable.MemoryRegion.Region:=⟨(pointer cursor).toNat,88⟩
  have valid : MutableTable.MemoryRegion.Valid region:=⟨buffer.lower,buffer.upper,aligned⟩
  have kept:=LocalFields.writes_outside memory region valid fields inside query (Or.inr (by change (pointer cursor).toNat+88≤query.toNat; omega))
  simpa only [region,MutableTable.MemoryRegion.pointer,BitVec.ofNat_toNat,BitVec.setWidth_eq] using kept

end InitECandidate.Solver.Mpt.WitnessRecord

#print axioms InitECandidate.Solver.Mpt.WitnessRecord.writes_above
