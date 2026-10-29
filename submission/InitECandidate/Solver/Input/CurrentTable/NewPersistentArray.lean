import InitECandidate.Solver.Input.CurrentTable.ArrayAllocation
import InitECandidate.Solver.Input.PersistentAllocationFrame

namespace InitECandidate.Solver.Input.CurrentTable.New
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

/-- Any of the real keys/nodes/order allocations and its metadata write
protect an earlier frontier. This frame is independent of key width and
array contents; request room is retained from the observed allocator return. -/
theorem array_persistent_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table cursor amount frontier : BitVec 64) (name : String) (offset : Nat)
    (tableArena : AllocatedBytes.Arena table 88) (inside : offset<88)
    (cursorArena : AllocatedBytes.Arena cursor 0) (room : cursor.toNat+amount.toNat≤2952790016)
    (beforeTable : frontier.toNat≤table.toNat) (beforeCursor : frontier.toNat≤cursor.toNat) :
    PersistentNormalFrame source (arrayEntry source table cursor amount name offset) frontier := by
  have checked:=PersistentAlloc.guards cursor amount room
  obtain ⟨nextCell,clock,locals,globals,memory⟩:=array_frame source table cursor amount name offset
  have nextArena : AllocatedBytes.Arena (PersistentAlloc.rounded cursor amount) 0:=
    ⟨by have low:=cursorArena.lower; have grow:=checked.2.2.1; omega,by have upper:=checked.2.2.2.1; omega⟩
  refine ⟨⟨_,nextCell,nextArena,checked.2.2.2.1,checked.2.2.2.2,by have grow:=checked.2.2.1; omega⟩,rfl,globals,?_⟩
  intro query before
  apply memory query
  have number:=byteAddress_toNat table offset (by have upper:=tableArena.upper; omega)
  change (table+BitVec.ofNat 64 offset).toNat=table.toNat+offset at number
  intro same
  have equal:=congrArg BitVec.toNat same
  rw [number] at equal
  omega

end InitECandidate.Solver.Input.CurrentTable.New

#print axioms InitECandidate.Solver.Input.CurrentTable.New.array_persistent_frame
