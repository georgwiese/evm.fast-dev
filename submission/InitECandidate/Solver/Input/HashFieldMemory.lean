import InitECandidate.Solver.Input.HashFieldSummary

namespace InitECandidate.Solver.Input.FixedHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Every actual normal original scalar/vector/copy field step preserves a
protected decoded word outside its field array and below temporary storage. -/
theorem Step.current_memory (step : Step) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (inputName : String) (p ch cursor stp accel chunk zeros query : BitVec 64)
    (inputLength fields temporaryLength : Nat) (valid : step.Fits inputLength fields temporaryLength)
    (protection : SszHash.Protected source stp accel chunk zeros query)
    (pointer : source.locals.lookup (ofString inputName)=some (.val (.word p)))
    (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (inputArena : AllocatedBytes.Arena p inputLength) (fieldArena : AllocatedBytes.Arena ch (32*fields)) (fieldAligned : ch.toNat%8=0)
    (arena : AllocatedBytes.Arena cursor temporaryLength) (aligned : cursor.toNat%8=0)
    (below : query.toNat<cursor.toNat) (fieldsAway : CopyGeneral.Away ch query (32*fields))
    (run : evaluateHOLFiniteState source (step.program inputName)=(none,post)) : post.memory query=source.memory query := by
  have inputSlice := AllocatedBytes.Arena.subrange p inputLength step.inputOffset step.length inputArena valid.1
  have outputSlice := AllocatedBytes.Arena.subrange ch (32*fields) (32*step.field) 32 fieldArena (by have h:=valid.2.1; omega)
  have outputNumber : (ch+BitVec.ofNat 64 (32*step.field)).toNat=ch.toNat+32*step.field := byteAddress_toNat ch (32*step.field) (by have h:=fieldArena.upper; have f:=valid.2.1; omega)
  have outputAligned : (ch+BitVec.ofNat 64 (32*step.field)).toNat%8=0 := by rw [outputNumber]; have h:=fieldAligned; omega
  have outputAway := CopyGeneral.Away.subrange ch query (32*fields) (32*step.field) 32 fieldsAway (by have h:=valid.2.1; omega)
  have args := step.arguments_read source inputName p ch pointer chunks
  cases step with
  | scalar offset field=>
    exact U64Hash.call_memory source post (p+BitVec.ofNat 64 offset) (ch+BitVec.ofNat 64 (32*field)) query
      protection.workspace.sha.installed protection.workspace.sha.domain inputSlice outputSlice outputAligned outputAway _ args run
  | copy offset field=>
    exact MemoryAt.copy_normal source post _ (p+BitVec.ofNat 64 offset) (ch+BitVec.ofNat 64 (32*field)) query 32 args
      protection.workspace.sha.installed protection.workspace.sha.domain inputSlice outputSlice outputAway run
  | vector offset length field depth=>
    have constraints := valid.2.2
    have temporary := AllocatedBytes.Arena.weaken cursor temporaryLength (832+96*PackBytes.chunks length) arena constraints.2.2.2
    exact BytesVector.call_memory source post (p+BitVec.ofNat 64 offset) cursor (ch+BitVec.ofNat 64 (32*field)) stp accel chunk zeros query length depth
      constraints.1 constraints.2.1 constraints.2.2.1 protection heap inputSlice temporary aligned outputSlice outputAligned below outputAway _ args run


end InitECandidate.Solver.Input.FixedHash

#print axioms InitECandidate.Solver.Input.FixedHash.Step.current_memory
