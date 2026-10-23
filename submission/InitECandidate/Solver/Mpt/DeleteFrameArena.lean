import InitECandidate.Solver.Arenas.ScopedTrace
import InitECandidate.Solver.MutableTable.MemoryRegionWord

namespace InitECandidate.Solver.Mpt.DeleteFrame
open Flapjack PanSemStateFiniteExact WitnessRadix

def ceiling : Nat:=2713717616

/-- The real forty-byte deletion records occupy the low scratch pool,
not the persistent heap. The cursor order is the allocator's current one. -/
theorem allocated_bounds (cursor frame : BitVec 64)
    (floor : 2701131776≤frame.toNat) (before : cursor.toNat≤ceiling)
    (aligned : frame.toNat%8=0) (room : Arenas.Room .down cursor frame 40#64) :
    let record:=Arenas.resultWord .down cursor 40#64
    AllocatedBytes.Arena record 40 ∧ record.toNat%8=0 ∧
      frame.toNat≤record.toNat ∧ record.toNat+40≤cursor.toNat ∧ record≠0#64 ∧
      MutableTable.MemoryRegion.Valid ⟨record.toNat,40⟩ := by
  have guards:=Arenas.downward_guards cursor frame 40#64 aligned room
  change frame.toNat+40≤cursor.toNat at room
  dsimp only [Arenas.resultWord]
  have recordFloor : 2701131776≤(Arenas.rounded .down cursor 40#64).toNat:=floor.trans guards.2.2.1
  have recordBefore : (Arenas.rounded .down cursor 40#64).toNat+40≤cursor.toNat:=guards.2.2.2.1
  have recordAligned := guards.2.2.2.2.2
  refine ⟨⟨recordFloor,?_⟩,recordAligned,guards.2.2.1,recordBefore,?_,⟨recordFloor,?_,recordAligned⟩⟩
  · change (Arenas.rounded .down cursor 40#64).toNat+40≤33806089496
    dsimp only [ceiling] at before; omega
  · intro zero
    rw [zero] at recordFloor
    contradiction
  · change (Arenas.rounded .down cursor 40#64).toNat+40≤33806089496
    dsimp only [ceiling] at before; omega

/-- Every true record field is a mapped word, including the extension's
last length word and the branch's saved child index at offset32. -/
theorem field_mapped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record : BitVec 64)
    (arena : AllocatedBytes.Arena record 40) (aligned : record.toNat%8=0)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (offset : Nat) (inside : offset<40) (wordAligned : offset%8=0) :
    source.memaddrs (byteAddress record offset) :=
  AllocatedBytes.word_mapped source record 40 offset domain arena inside aligned wordAligned

end InitECandidate.Solver.Mpt.DeleteFrame

#print axioms InitECandidate.Solver.Mpt.DeleteFrame.allocated_bounds
#print axioms InitECandidate.Solver.Mpt.DeleteFrame.field_mapped
