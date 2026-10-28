import InitECandidate.Solver.Input.CurrentTable.NodeBuild.LoopSyntax
import InitECandidate.Solver.Input.CurrentTable.ImageFacts
import InitECandidate.Solver.Headers.ValidateRows

namespace InitECandidate.Solver.Input.CurrentTable.NodeBuild
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Fixed arguments of one real current node/code database builder. -/
structure Data where
  array : BitVec 64
  table : BitVec 64
  cap : BitVec 64
  out : BitVec 64
  stp : BitVec 64
  pad : BitVec 64
  pointers : Nat → BitVec 64
  lengths : Nat → BitVec 64
  total : Nat
  lower : Nat
  upper : Nat
  itemLimit : Nat

def ValueOf (data : Data) (value : BitVec 64) : Prop :=
  ∃ index<data.total,value=byteAddress data.array (16*index)

structure Layout (data : Data) : Prop where
  totalSmall : data.total<2^31
  capacity : 2*data.total+2≤data.cap.toNat
  inputBefore : data.upper≤data.table.toNat
  stateBefore : data.stp.toNat+200≤data.lower
  padBefore : data.pad.toNat+136≤data.lower
  outBefore : data.out.toNat+32≤data.lower
  outArena : AllocatedBytes.Arena data.out 32
  outAligned : data.out.toNat%8=0
  lowerUpper : data.lower≤data.upper
  lowerSmall : data.lower<2^64
  lengths : ∀ index<data.total,(data.lengths index).toNat≤data.itemLimit
  itemSmall : data.itemLimit+136<2^64

/-- Physical rows, live counter and the actual insertion history. The
current image has at most one leaf per processed row; all stored values
are addresses of genuine decoded records from this same array. -/
structure State (data : Data) (origin current : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat) : Prop where
  arena : CurrentStartup.ArenaState current
  little : current.be=false
  environment : CurrentKeccak.Hash.Environment current data.stp data.pad
  outCell : current.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word data.out))
  rows : Headers.Validate.Rows current data.array data.pointers data.lengths data.total data.lower data.upper
  input : HashInput.Frame origin current data.lower data.upper
  heap : NormalHeapEffects.AtLeast (New.endPointer data.table data.cap).toNat current
  globals : ∀ key,current.globals.lookup key=origin.globals.lookup key
  arrayCell : current.locals.lookup (ofString "slice_arr")=some (.val (.word data.array))
  countCell : current.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 data.total)))
  tableCell : current.locals.lookup (ofString "t")=some (.val (.word data.table))
  indexCell : current.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))
  image : ∃ root next count valid bits left right keys,
    Image current data.table data.cap root next count valid bits left right keys (ValueOf data) ∧ count≤index

/-- Entering the actual while body changes only the paid loop clock. -/
theorem State.dec_clock (data : Data) (origin current : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : State data origin current index) : State data origin (decClockHOLFinite current) index := by
  obtain ⟨root,next,count,valid,bits,left,right,keys,image,bound⟩ := state.image
  exact ⟨state.arena.of_frame rfl,state.little,state.environment.of_frame rfl,state.outCell,
    state.rows.of_frame current _ data.array data.pointers data.lengths data.total data.lower data.upper ⟨by intros; rfl⟩,
    ⟨state.input.words⟩,state.heap,state.globals,state.arrayCell,state.countCell,state.tableCell,state.indexCell,
    root,next,count,valid,bits,left,right,keys,image.of_frame rfl,bound⟩

end InitECandidate.Solver.Input.CurrentTable.NodeBuild

#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.State.dec_clock
