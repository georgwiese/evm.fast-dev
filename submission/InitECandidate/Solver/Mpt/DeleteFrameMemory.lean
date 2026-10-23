import InitECandidate.Solver.Mpt.DeleteFrameProgram
import InitECandidate.Solver.Mpt.DeleteFrameArena

namespace InitECandidate.Solver.Mpt.DeleteFrame
open Flapjack PanSemStateFiniteExact WitnessRadix

def written (kind : Kind) (memory : WordWrites.Memory) (record : BitVec 64) (words : String→BitVec 64) : WordWrites.Memory:=
  WordWrites.write memory (LocalFields.writes record (kind.fields words))

/-- Only the four branch fields or five extension fields that the actual
program initializes are asserted; branch offset24 remains unrestricted. -/
theorem written_cells (kind : Kind) (memory : WordWrites.Memory) (record : BitVec 64) (words : String→BitVec 64) :
    ∀ field∈kind.fields words,written kind memory record words (record+BitVec.ofNat 64 field.offset)=.word field.value.word := by
  intro field member
  exact WordWrites.write_unique memory (LocalFields.writes record (kind.fields words))
    (record+BitVec.ofNat 64 field.offset,field.value.word) (kind.fields_distinct words record) (List.mem_map.mpr ⟨field,member,rfl⟩)

/-- A real push preserves every older scratch record above its incoming
cursor, all persistent memory, and the caller frame below its limit. -/
theorem written_outside (kind : Kind) (memory : WordWrites.Memory) (record : BitVec 64) (words : String→BitVec 64)
    (arena : AllocatedBytes.Arena record 40) (aligned : record.toNat%8=0)
    (query : BitVec 64) (outside : query.toNat<record.toNat ∨ record.toNat+40≤query.toNat) :
    written kind memory record words query=memory query := by
  let region : MutableTable.MemoryRegion.Region:=⟨record.toNat,40⟩
  have valid : MutableTable.MemoryRegion.Valid region:=⟨arena.lower,arena.upper,aligned⟩
  have kept:=LocalFields.writes_outside memory region valid (kind.fields words)
    (by intro field member; have inside:=(kind.geometry words field member).1; change field.offset<40; omega) query outside
  simpa only [written,region,MutableTable.MemoryRegion.pointer,BitVec.ofNat_toNat,BitVec.setWidth_eq] using kept

theorem allocated_writes_above (kind : Kind) (memory : WordWrites.Memory) (cursor frame : BitVec 64) (words : String→BitVec 64)
    (floor : 2701131776≤frame.toNat) (before : cursor.toNat≤ceiling)
    (aligned : frame.toNat%8=0) (room : Arenas.Room .down cursor frame 40#64)
    (query : BitVec 64) (above : cursor.toNat≤query.toNat) :
    written kind memory (Arenas.resultWord .down cursor 40#64) words query=memory query := by
  obtain ⟨arena,recordAligned,_,recordBefore,_,_⟩:=allocated_bounds cursor frame floor before aligned room
  exact written_outside kind memory _ words arena recordAligned query (Or.inr (recordBefore.trans above))

end InitECandidate.Solver.Mpt.DeleteFrame

#print axioms InitECandidate.Solver.Mpt.DeleteFrame.written_cells
#print axioms InitECandidate.Solver.Mpt.DeleteFrame.written_outside
#print axioms InitECandidate.Solver.Mpt.DeleteFrame.allocated_writes_above
