import InitECandidate.Solver.Input.ShaPairProgram
import InitECandidate.Solver.Input.ShaBlockInPlace

namespace InitECandidate.Solver.Input.ShaPair
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch ShaFixedCost

private theorem copy_price (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b stp accel src : BitVec 64)
    (actual : Ready source a b stp accel) (name : String) (bytes : Nat) (inside : bytes+32≤96)
    (inputLocal : source.locals.lookup (ofString name)=some (.val (.word src)))
    (inputArena : AllocatedBytes.Arena src 32) (workspaceArena : AllocatedBytes.Arena accel 96) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memcpy") (copyArguments name bytes))).2.clock≤5 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) (copyArguments name bytes)=
      some (CopyGeneral.values (accel+BitVec.ofNat 64 bytes) src 32) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,copyArguments,offset,global,localVar,inputLocal,actual.accelerator,
      CopyGeneral.values,valueIsWord,valueWord,wordOpHOL,wordOp]
  have destination : AllocatedBytes.Arena (accel+BitVec.ofNat 64 bytes) 32 := AllocatedBytes.Arena.subrange accel 96 bytes 32 workspaceArena inside
  have cost := CopyGeneral.call_cost_arena source (copyArguments name bytes) src (accel+BitVec.ofNat 64 bytes) 32 args
    (CopyGeneral.original_code source.code actual.installed) actual.domain inputArena destination
  have blocks := CopyGeneral.cost_word_multiple src (accel+BitVec.ofNat 64 bytes) 32 (by decide)
  omega

private theorem clear_price (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b stp accel : BitVec 64)
    (actual : Ready source a b stp accel) (workspaceArena : AllocatedBytes.Arena accel 96) (aligned : accel.toNat%8=0) :
    source.clock-(evaluateHOLFiniteState source Stage.clear.program).2.clock≤3 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [offset "sha_accel" 32,.const 64#64]=
      some (Zero.values (accel+32#64) 64) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,offset,global,actual.accelerator,Zero.values,valueIsWord,valueWord,wordOpHOL,wordOp]
  have destination : AllocatedBytes.Arena (accel+32#64) 64 := AllocatedBytes.Arena.subrange accel 96 32 64 workspaceArena (by decide)
  have number : (accel+32#64).toNat=accel.toNat+32 := byteAddress_toNat accel 32 (by have upper := workspaceArena.upper; omega)
  have destinationAligned : (accel+32#64).toNat%8=0 := by rw [number,Nat.add_mod,aligned]
  have cost := Zero.call_cost source [offset "sha_accel" 32,.const 64#64] (accel+32#64) 64 args
    (Zero.original_code source.code actual.installed) (by decide) (by decide) destinationAligned
    (by intro index inside multiple; exact AllocatedBytes.word_mapped source _ 64 index actual.domain destination (by omega) destinationAligned multiple)
  exact cost

/-- Each literal original pair stage is priced at its current real state.
Input and workspace mapping are entry facts; no future success is assumed. -/
theorem Stage.cost (stage : Stage) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b stp accel : BitVec 64)
    (actual : Ready source a b stp accel) (aArena : AllocatedBytes.Arena a 32) (bArena : AllocatedBytes.Arena b 32)
    (workspaceArena : AllocatedBytes.Arena accel 96) (aligned : accel.toNat%8=0) :
    source.clock-(evaluateHOLFiniteState source stage.program).2.clock≤stage.price := by
  have blockArgs : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) blockArguments=
      some (blockValues stp (accel+32#64)) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,blockArguments,offset,global,actual.accelerator,actual.state,
      blockValues,valueIsWord,valueWord,wordOpHOL,wordOp]
  have blockCost := block_in_place_call_price source stp accel actual.installed (some none) blockArguments blockArgs actual.accelerator
  cases stage with
  | «initialize»=>exact initialize_call_price source.code actual.installed (some none) _ source rfl
  | copyA=>exact copy_price source a b stp accel a actual "input_a" 32 (by decide) actual.inputA aArena workspaceArena
  | copyB=>exact copy_price source a b stp accel b actual "input_b" 64 (by decide) actual.inputB bArena workspaceArena
  | firstBlock=>exact blockCost
  | clear=>exact clear_price source a b stp accel actual workspaceArena aligned
  | padding=>exact ClockCost.store_byte source.code _ _ source rfl
  | length=>exact GasBudget.MemoryWriter.call_price .be64 source.code actual.installed (some none) _ 2 (GasBudget.MemoryWriter.be64_price source.code actual.installed) source rfl
  | secondBlock=>exact blockCost
  | finish=>exact finish_call_price source.code actual.installed (some none) _ source rfl

theorem program_cost (steps : List Stage) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b stp accel : BitVec 64)
    (actual : Ready source a b stp accel) (aArena : AllocatedBytes.Arena a 32) (bArena : AllocatedBytes.Arena b 32)
    (workspaceArena : AllocatedBytes.Arena accel 96) (aligned : accel.toNat%8=0) :
    source.clock-(evaluateHOLFiniteState source (program steps)).2.clock≤price steps := by
  induction steps generalizing source with
  | nil=>exact ClockCost.returned source.code _ source rfl
  | cons stage rest ih=>
    apply ClockCost.sequence_reached_current source stage.program (program rest) stage.price (price rest)
      (stage.cost source a b stp accel actual aArena bArena workspaceArena aligned)
    intro middle normal
    exact ih middle (stage.ready source middle a b stp accel actual normal)

/-- Complete unchanged sha256_pair, including both original block calls,
copy/zero/padding/writer/finish and every abnormal outcome. Source ticks are
separate from its accelerator and straight-line target instruction work. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b stp accel : BitVec 64)
    (actual : Ready source a b stp accel) (aArena : AllocatedBytes.Arena a 32) (bArena : AllocatedBytes.Arena b 32)
    (workspaceArena : AllocatedBytes.Arena accel 96) (aligned : accel.toNat%8=0) :
    source.clock-(evaluateHOLFiniteState source pairBody).2.clock≤52 := by
  rw [original_shape]
  simpa only [total_price] using program_cost stages source a b stp accel actual aArena bArena workspaceArena aligned

end InitECandidate.Solver.Input.ShaPair

#print axioms InitECandidate.Solver.Input.ShaPair.Stage.cost
#print axioms InitECandidate.Solver.Input.ShaPair.program_cost
#print axioms InitECandidate.Solver.Input.ShaPair.body_cost
