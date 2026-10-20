import InitECandidate.Solver.Input.Be64Execution

namespace InitECandidate.Solver.Input.MemoryWordCalls
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
open GasBudget.MemoryWriter

private theorem fast_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer word : BitVec 64) :
    (fastPost source pointer word).clock = source.clock - 1 := rfl
private theorem fast_control (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer word : BitVec 64) :
    KeccakAbsorb.hashControl (fastPost source pointer word) = KeccakAbsorb.hashControl source := rfl
private theorem slow_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer word : BitVec 64) :
    (slowPost source pointer word).clock = source.clock - 2 := rfl
private theorem slow_control (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer word : BitVec 64) :
    KeccakAbsorb.hashControl (emptyLocalsHOLFinite (slowPost source pointer word)) = KeccakAbsorb.hashControl source := rfl

/-- Current ABI cells and mapped bytes give an actual original writer
return on both alignment branches, without a future normal-run premise. -/
theorem be64_body_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer value : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (p : source.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (v : source.locals.lookup (ofString "v") = some (.val (.word value)))
    (mapped : BytesMapped source pointer 8) (enough : 2 ≤ source.clock) :
    ∃ post,evaluateHOLFiniteState source Kind.be64.body = (some (.returned (.val (.word 0#64))),post) ∧
      post.clock ≤ source.clock ∧ source.clock - 2 ≤ post.clock ∧ KeccakAbsorb.hashControl post = KeccakAbsorb.hashControl source := by
  classical
  by_cases aligned : pointer &&& 7#64 = 0#64
  · have key : panByteAlignHOL (width := 64) pointer = pointer := by
      apply BitVec.eq_of_toNat_eq
      rw [AllocatedBytes.aligned_number]
      have remainder := AllocatedBytes.mask_aligned pointer aligned
      omega
    have pointerMapped : source.memaddrs pointer := by simpa only [byteAddress,show BitVec.ofNat 64 0 = 0#64 from rfl,BitVec.add_zero,key] using mapped 0 (by decide)
    have run := be64_fast_execute source pointer value installed p v pointerMapped (by omega)
    let post := fastPost source pointer (BswapExecution.result value)
    have clock : post.clock = source.clock - 1 := fast_clock source pointer (BswapExecution.result value)
    have branch : evaluateHOLFiniteState source (.ite (fastTest .be64) (fast .be64) .skip) = (some (.returned (.val (.word 0#64))),post) := by
      rw [be64_test,evaluateHOLFiniteState_ite]
      have selected : QueryBranch.eval source (.cmp .equal (.op .and [localVar "p",.const 7#64]) (.const 0#64)) = some (.val (.word 1#64)) := by
        simp [QueryBranch.eval,evalHOLExact,evalListHOLExact,localVar,p,valueIsWord,valueWord,wordOpHOL,wordOp,AndOp.and,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,aligned]
      simp only [QueryBranch.eval] at selected
      rw [selected]
      exact run
    refine ⟨post,?_,by omega,by omega,fast_control source pointer (BswapExecution.result value)⟩
    rw [guarded_body .be64 (Or.inl rfl)]
    exact StateSteps.stopped_sequence source post _ _ (.returned (.val (.word 0#64))) branch (by omega)
  · have branch : evaluateHOLFiniteState source (.ite (fastTest .be64) (fast .be64) .skip) = (none,source) := by
      rw [be64_test,evaluateHOLFiniteState_ite]
      have selected : QueryBranch.eval source (.cmp .equal (.op .and [localVar "p",.const 7#64]) (.const 0#64)) = some (.val (.word 0#64)) := by
        simp [QueryBranch.eval,evalHOLExact,evalListHOLExact,localVar,p,valueIsWord,valueWord,wordOpHOL,wordOp,AndOp.and,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,aligned]
      simp only [QueryBranch.eval] at selected
      rw [selected]
      simp [evaluateHOLFiniteState_skip]
    have run := be64_slow_execute source pointer value installed p v mapped enough
    let post := emptyLocalsHOLFinite (slowPost source pointer value)
    have clock : post.clock = source.clock - 2 := slow_clock source pointer value
    refine ⟨post,?_,by omega,by omega,slow_control source pointer value⟩
    rw [guarded_body .be64 (Or.inl rfl),StateSteps.next_sequence source source _ _ branch (Nat.le_refl _)]
    exact run

theorem be64_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer value : BitVec 64) (arguments : List (ExpHOL 64))
    (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) arguments = some [.val (.word pointer),.val (.word value)])
    (mapped : BytesMapped source pointer 8) (enough : 3 ≤ source.clock) :
    ∃ post,evaluateHOLFiniteState source (.call (some (none,none)) (ofString "st_be64") arguments) = (none,post) ∧
      post.locals = source.locals ∧ post.clock ≤ source.clock ∧ source.clock - 3 ≤ post.clock ∧ KeccakAbsorb.hashControl post = KeccakAbsorb.hashControl source := by
  obtain ⟨callee,called,p,v⟩ := environment source.code.lookup (ofString "st_be64") Kind.be64.body pointer value (be64_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨target,run,upper,lower,control⟩ := be64_body_execute entry pointer value installed p v mapped (by change 2 ≤ source.clock - 1; omega)
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "st_be64") arguments [.val (.word pointer),.val (.word value)] _ callee .one
    (.val (.word 0#64)) target args called (by omega) run (by simp [shapeOfHOLExact,shapeEqHOL])
  refine ⟨{target with locals := source.locals},actual,rfl,?_,?_,?_⟩
  · change target.clock ≤ source.clock
    change target.clock ≤ source.clock - 1 at upper
    omega
  · change source.clock - 3 ≤ target.clock
    change source.clock - 1 - 2 ≤ target.clock at lower
    omega
  · exact control

end InitECandidate.Solver.Input.MemoryWordCalls

#print axioms InitECandidate.Solver.Input.MemoryWordCalls.be64_body_execute
#print axioms InitECandidate.Solver.Input.MemoryWordCalls.be64_execute
