import InitECandidate.Solver.Input.PureReturn
import InitECandidate.Solver.WitnessRadix.WordWrites

namespace InitECandidate.Solver.GasBudget
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

abbrev Memory := WitnessRadix.WordWrites.Memory
def frameAddress (offset : BitVec 64) : ExpHOL 64 := .op .add [.var .global (ofString "ev"),.const offset]
def frameLoad (offset : BitVec 64) : ExpHOL 64 := .load .one (frameAddress offset)
def wordAt (memory : Memory) (address : BitVec 64) : BitVec 64 := WitnessRadix.MemoryBytes.wordBits (memory address)

theorem address_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame offset : BitVec 64)
    (ev : source.globals.lookup (ofString "ev")=some (.val (.word frame))) :
    eval source (frameAddress offset)=some (.val (.word (frame+offset))) := by
  simp [eval,frameAddress,evalHOLExact,evalListHOLExact,toExact,ev,valueIsWord,valueWord,wordOpHOL,wordOp]

theorem frame_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame offset value : BitVec 64)
    (ev : source.globals.lookup (ofString "ev")=some (.val (.word frame)))
    (mapped : source.memaddrs (frame+offset)) (stored : source.memory (frame+offset)=.word value) :
    eval source (frameLoad offset)=some (.val (.word value)) := by
  simp [eval,frameLoad,frameAddress,evalHOLExact,evalListHOLExact,toExact,ev,valueIsWord,valueWord,wordOpHOL,wordOp,
    memLoadHOLExact,isWfShapeExactHOL,mapped,stored]

theorem offsets_ne (frame first second : BitVec 64) (different : first≠second) : frame+first≠frame+second := by
  intro same
  exact different ((BitVec.add_right_inj frame).mp same)

/-- The regular counter, liquid regular gas and outstanding state spill form
the regular budget. State-reservoir credits do not enter this sum directly. -/
def regularBudget (memory : Memory) (frame : BitVec 64) : Nat :=
  (wordAt memory (frame+64#64)).toNat+(wordAt memory (frame+184#64)).toNat+(wordAt memory (frame+192#64)).toNat

end InitECandidate.Solver.GasBudget

#print axioms InitECandidate.Solver.GasBudget.address_read
#print axioms InitECandidate.Solver.GasBudget.frame_read
#print axioms InitECandidate.Solver.GasBudget.offsets_ne
