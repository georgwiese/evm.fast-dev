import InitECandidate.Solver.Input.ShaInitializeMemory
import InitECandidate.Solver.Input.ShaBlockMemory
import InitECandidate.Solver.Input.ShaFinishCallMemory
import InitECandidate.Solver.Input.Be64Memory
import InitECandidate.Solver.Input.CopyZeroMemoryNormal
import InitECandidate.Solver.Input.ShaPairProgram

namespace InitECandidate.Solver.Input.ShaPair
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

structure MemoryReady (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b out stp accel : BitVec 64) : Prop where
  actual : Ready source a b stp accel
  output : source.locals.lookup (ofString "out")=some (.val (.word out))

theorem MemoryReady.after (stage : Stage) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (a b out stp accel : BitVec 64)
    (ready : MemoryReady source a b out stp accel) (run : evaluateHOLFiniteState source stage.program=(none,post)) : MemoryReady post a b out stp accel :=
  ⟨stage.ready source post a b stp accel ready.actual run,(stage.locals (ofString "out") source post run).trans ready.output⟩

private theorem copy_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (inputName : String) (input accel query : BitVec 64) (bytes : Nat)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointer : source.locals.lookup (ofString inputName)=some (.val (.word input)))
    (accelerator : source.globals.lookup (ofString "sha_accel")=some (.val (.word accel)))
    (inputArena : AllocatedBytes.Arena input 32) (arena : AllocatedBytes.Arena accel 96) (inside : bytes+32≤96)
    (away : CopyGeneral.Away accel query 96)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memcpy") (copyArguments inputName bytes))=(none,post)) : post.memory query=source.memory query := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) (copyArguments inputName bytes)=some (CopyGeneral.values (accel+BitVec.ofNat 64 bytes) input 32) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,copyArguments,offset,global,localVar,pointer,accelerator,CopyGeneral.values,valueIsWord,valueWord,wordOpHOL,wordOp]
  exact MemoryAt.copy_normal source post _ input (accel+BitVec.ofNat 64 bytes) query 32 args installed domain inputArena
    (AllocatedBytes.Arena.subrange accel 96 bytes 32 arena inside) (CopyGeneral.Away.subrange accel query 96 bytes 32 away inside) run

/-- Each real original pair stage preserves a protected word outside its
state, accelerator and output. Mapping is current physical geometry; all
normal callee returns are derived from that same stage invocation. -/
theorem Stage.memory (stage : Stage) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (a b out stp accel query : BitVec 64)
    (ready : MemoryReady source a b out stp accel)
    (aArena : AllocatedBytes.Arena a 32) (bArena : AllocatedBytes.Arena b 32) (arena : AllocatedBytes.Arena accel 96) (aligned : accel.toNat%8=0)
    (stateAway : CopyGeneral.Away stp query 64) (accelAway : CopyGeneral.Away accel query 96) (outAway : CopyGeneral.Away out query 32)
    (run : evaluateHOLFiniteState source stage.program=(none,post)) : post.memory query=source.memory query := by
  cases stage with
  | «initialize»=>
    have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [global "sha_st"]=some [.val (.word stp)] := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,global,ready.actual.state]
    exact ShaFixedCost.initialize_call_memory source post stp query _ ready.actual.installed args stateAway run
  | copyA=>exact copy_memory source post "input_a" a accel query 32 ready.actual.installed ready.actual.domain ready.actual.inputA ready.actual.accelerator aArena arena (by decide) accelAway run
  | copyB=>exact copy_memory source post "input_b" b accel query 64 ready.actual.installed ready.actual.domain ready.actual.inputB ready.actual.accelerator bArena arena (by decide) accelAway run
  | firstBlock | secondBlock=>
    have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) blockArguments=some (ShaFixedCost.blockValues stp (accel+32#64)) := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,blockArguments,global,offset,ready.actual.state,ready.actual.accelerator,ShaFixedCost.blockValues,valueIsWord,valueWord,wordOpHOL,wordOp]
    exact ShaFixedCost.block_in_place_call_memory source post stp accel query blockArguments ready.actual.installed ready.actual.accelerator args stateAway accelAway run
  | clear=>
    have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [offset "sha_accel" 32,.const 64#64]=some (Zero.values (accel+32#64) 64) := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,offset,global,ready.actual.accelerator,Zero.values,valueIsWord,valueWord,wordOpHOL,wordOp]
    have buffer := AllocatedBytes.Arena.subrange accel 96 32 64 arena (by decide)
    have number : (accel+32#64).toNat=accel.toNat+32 := byteAddress_toNat accel 32 (by have h:=arena.upper; omega)
    exact MemoryAt.zero_normal source post _ (accel+32#64) query 64 args ready.actual.installed ready.actual.domain buffer (by rw [number]; omega) (by decide)
      (by intro offset inside; exact (CopyGeneral.Away.subrange accel query 96 32 64 accelAway (by decide) offset inside).1) run
  | padding=>
    have read : eval source (offset "sha_accel" 32)=some (.val (.word (accel+32#64))) := by
      simp [eval,evalHOLExact,evalListHOLExact,toExact,offset,global,ready.actual.accelerator,valueIsWord,valueWord,wordOpHOL,wordOp]
    have frame := MemoryAt.byte_store_current source (offset "sha_accel" 32) (.const 128#64) (accel+32#64) query read (accelAway 32 (by decide)).2
    change (evaluateHOLFiniteState source Stage.padding.program).2.memory query=source.memory query at frame
    rw [run] at frame
    exact frame
  | length=>
    have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [offset "sha_accel" 88,.const 512#64]=some [.val (.word (accel+88#64)),.val (.word 512#64)] := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,offset,global,ready.actual.accelerator,valueIsWord,valueWord,wordOpHOL,wordOp]
    exact MemoryWordCalls.be64_call_memory source post _ (accel+88#64) 512#64 query ready.actual.installed ready.actual.domain args
      (AllocatedBytes.Arena.subrange accel 96 88 8 arena (by decide)) (CopyGeneral.Away.subrange accel query 96 88 8 accelAway (by decide)) run
  | finish=>
    have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [global "sha_st",localVar "out"]=some (ShaFixedCost.finishValues stp out) := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,global,localVar,ready.actual.state,ready.output,ShaFixedCost.finishValues]
    exact ShaFixedCost.finish_call_memory source post stp out query _ ready.actual.installed args outAway run

end InitECandidate.Solver.Input.ShaPair

#print axioms InitECandidate.Solver.Input.ShaPair.MemoryReady.after
#print axioms InitECandidate.Solver.Input.ShaPair.Stage.memory
