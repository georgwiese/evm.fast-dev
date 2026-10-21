import InitECandidate.Solver.Input.ShaBlockMemoryProgram
import InitECandidate.Solver.Input.ScalarStoreMemory
import InitECandidate.Solver.Input.MemoryContinue

namespace InitECandidate.Solver.Input.ShaFixedCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

private theorem packed_address_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (accel : BitVec 64) (index : Nat)
    (accelerator : source.globals.lookup (ofString "sha_accel")=some (.val (.word accel)))
    (position : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    eval source packedAddress=some (.val (.word (accel+BitVec.ofNat 64 (8*index)))) := by
  simp [eval,packedAddress,evalHOLExact,evalListHOLExact,toExact,localVar,accelerator,position,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,BitVec.ofNat_mul,Nat.mul_comm]

theorem first_tail_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (accel query : BitVec 64) (index : Nat)
    (active : index<4) (accelerator : source.globals.lookup (ofString "sha_accel")=some (.val (.word accel)))
    (position : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (away : CopyGeneral.Away accel query 96) (run : evaluateHOLFiniteState source firstMemoryTail=(none,post)) : post.memory query=source.memory query := by
  obtain ⟨middle,normal,remaining⟩ := sequence_none source post _ increment run
  have stored := MemoryAt.op_store_normal source middle packedAddress .or packedArguments (accel+BitVec.ofNat 64 (8*index)) query
    (packed_address_read source accel index accelerator position) (away (8*index) (by omega)).1 normal
  have assigned := MemoryAt.assign_current middle .local (ofString "i") (.op .add [localVar "i",.const 1#64]) query
  change evaluateHOLFiniteState middle (.assign .local (ofString "i") (.op .add [localVar "i",.const 1#64]))=(none,post) at remaining
  rw [remaining] at assigned
  exact assigned.trans stored

/-- The actual pack iteration only changes one accelerator state word.
Normal declarations derive their own successful reads; loaded data is free. -/
theorem first_step_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (accel query : BitVec 64) (index : Nat)
    (active : index<4) (accelerator : source.globals.lookup (ofString "sha_accel")=some (.val (.word accel)))
    (position : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (away : CopyGeneral.Away accel query 96) (run : evaluateHOLFiniteState source firstStep=(none,post)) : post.memory query=source.memory query := by
  rw [first_memory_shape] at run
  refine MemoryAt.declaration_normal source post "lo" .one (.load .one stateAddress) _ query ?_ run
  intro loValue loPost loRun
  let loEntry := setVarHOLFinite (ofString "lo") loValue source
  have loPosition : loEntry.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))) :=
    (MemoryAt.set_lookup_other source (ofString "lo") (ofString "i") loValue (by decide)).trans position
  refine MemoryAt.declaration_normal loEntry loPost "hi" .one (.load .one stateAddressHi) firstMemoryTail query ?_ loRun
  intro hiValue hiPost hiRun
  have hiPosition := (MemoryAt.set_lookup_other loEntry (ofString "hi") (ofString "i") hiValue (by decide)).trans loPosition
  exact first_tail_memory (setVarHOLFinite (ofString "hi") hiValue loEntry) hiPost accel query index active accelerator hiPosition away hiRun

private theorem state_address_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (index : Nat)
    (state : source.locals.lookup (ofString "stp")=some (.val (.word pointer)))
    (position : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    eval source stateAddress=some (.val (.word (pointer+BitVec.ofNat 64 (16*index)))) ∧
      eval source stateAddressHi=some (.val (.word (pointer+BitVec.ofNat 64 (16*index+8)))) := by
  constructor <;> simp [eval,stateAddress,stateAddressHi,evalHOLExact,evalListHOLExact,toExact,localVar,state,position,valueIsWord,valueWord,
    wordOpHOL,wordOp,panOpHOL,BitVec.ofNat_mul,BitVec.ofNat_add,Nat.mul_comm,BitVec.add_assoc]

theorem second_tail_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64) (index : Nat)
    (active : index<4) (state : source.locals.lookup (ofString "stp")=some (.val (.word pointer)))
    (position : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (away : CopyGeneral.Away pointer query 64) (run : evaluateHOLFiniteState source secondMemoryTail=(none,post)) : post.memory query=source.memory query := by
  obtain ⟨middle,firstRun,tailRun⟩ := sequence_none source post _ _ run
  obtain ⟨last,secondRun,assignRun⟩ := sequence_none middle post _ increment tailRun
  have firstFrame := MemoryAt.shift_store_normal source middle stateAddress .lsr stateLowValue (.const 32#64) (pointer+BitVec.ofNat 64 (16*index)) query
    (state_address_read source pointer index state position).1 (away (16*index) (by omega)).1 firstRun
  have current := store_none_frame source middle _ _ firstRun
  have nextState : middle.locals.lookup (ofString "stp")=some (.val (.word pointer)) := by rw [current]; exact state
  have nextPosition : middle.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))) := by rw [current]; exact position
  have secondFrame := MemoryAt.shift_store_normal middle last stateAddressHi .lsr (localVar "packed") (.const 32#64) (pointer+BitVec.ofNat 64 (16*index+8)) query
    (state_address_read middle pointer index nextState nextPosition).2 (away (16*index+8) (by omega)).1 secondRun
  have assigned := MemoryAt.assign_current last .local (ofString "i") (.op .add [localVar "i",.const 1#64]) query
  change evaluateHOLFiniteState last (.assign .local (ofString "i") (.op .add [localVar "i",.const 1#64]))=(none,post) at assignRun
  rw [assignRun] at assigned
  exact assigned.trans (secondFrame.trans firstFrame)

/-- The actual unpack iteration only changes its two SHA state words. -/
theorem second_step_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer query : BitVec 64) (index : Nat)
    (active : index<4) (state : source.locals.lookup (ofString "stp")=some (.val (.word pointer)))
    (position : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (away : CopyGeneral.Away pointer query 64) (run : evaluateHOLFiniteState source secondStep=(none,post)) : post.memory query=source.memory query := by
  rw [second_memory_shape] at run
  refine MemoryAt.declaration_normal source post "packed" .one (.load .one packedAddress) secondMemoryTail query ?_ run
  intro packedValue inner remaining
  have nextState := (MemoryAt.set_lookup_other source (ofString "packed") (ofString "stp") packedValue (by decide)).trans state
  have nextPosition := (MemoryAt.set_lookup_other source (ofString "packed") (ofString "i") packedValue (by decide)).trans position
  exact second_tail_memory (setVarHOLFinite (ofString "packed") packedValue source) inner pointer query index active nextState nextPosition away remaining

end InitECandidate.Solver.Input.ShaFixedCost

#print axioms InitECandidate.Solver.Input.ShaFixedCost.first_tail_memory
#print axioms InitECandidate.Solver.Input.ShaFixedCost.first_step_memory
#print axioms InitECandidate.Solver.Input.ShaFixedCost.second_tail_memory
#print axioms InitECandidate.Solver.Input.ShaFixedCost.second_step_memory
