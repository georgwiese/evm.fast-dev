import InitECandidate.Solver.Headers.FieldRowArguments
import InitECandidate.Solver.Input.CurrentStartup.ArenaFrame

namespace InitECandidate.Solver.Headers.CurrentHelpers
open Flapjack PanSemStateFiniteExact
open Input WitnessRadix

/-- Actual input encodings and their physical records. Initialized arenas
replace the obsolete mapped-scratch model; no future helper result is stored. -/
structure SliceImage (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer array : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem) : Prop where
  itemsAtInput : Rlp.ListItems source pointer bytes items
  records : Rlp.Slices.Records source.memory array pointer items
  arena : CurrentStartup.ArenaState source
  arrayArena : AllocatedBytes.Arena array (16*items.length)
  arrayAligned : array.toNat%8=0
  inputFits : pointer.toNat+bytes<2^64
  inputBefore : pointer.toNat+bytes≤array.toNat

theorem SliceImage.of_frame {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer array : BitVec 64} {bytes : Nat} {items : List Rlp.ListItem}
    (data : SliceImage source pointer array bytes items) (frame : LocalEffects.erase post=LocalEffects.erase source) :
    SliceImage post pointer array bytes items := by
  have memory:=congrArg PanSemStateFiniteExact.memory frame
  change post.memory=source.memory at memory
  refine ⟨?_,by rw [memory]; exact data.records,data.arena.of_frame frame,data.arrayArena,data.arrayAligned,data.inputFits,data.inputBefore⟩
  apply Rlp.ListItems.transport source post pointer bytes items data.itemsAtInput (by have h:=data.inputFits; omega)
  intro offset inside
  change Rlp.ReadLength.byte (LocalEffects.erase source) _=Rlp.ReadLength.byte (LocalEffects.erase post) _
  rw [frame]

end InitECandidate.Solver.Headers.CurrentHelpers

#print axioms InitECandidate.Solver.Headers.CurrentHelpers.SliceImage.of_frame
