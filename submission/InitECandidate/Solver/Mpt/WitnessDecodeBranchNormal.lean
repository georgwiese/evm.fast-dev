import InitECandidate.Solver.Mpt.WitnessDecodeRecordInputs
import InitECandidate.Solver.Mpt.WitnessDecodeRecordFrame
import InitECandidate.Solver.Mpt.NodeBranchNormal
import InitECandidate.Solver.Mpt.FailGuardReturn
import InitECandidate.Solver.Input.MainEntry
import InitECandidate.Solver.Input.CallResumeLookup
import InitECandidate.Solver.Rlp.SlicesNormal

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def branchAllocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) : PanSemStateFiniteExact 64 Guest.HostMemory:=
  {PersistentAlloc.post {source with clock:=source.clock-10} heap 176#64 with
    memory:=StoreWord.put (Zero.finalMemory source.memory heap 176) heap 3#64}

/-- A real original branch return enforces count17, constructs its genuine
zeroed176-byte node and initializes the actual88-byte scratch record. Room,
record progress and all physical post-state bytes follow from that execution. -/
theorem branch_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer length count heap cursor limit : BitVec 64)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (sliceCell : source.locals.lookup (ofString "sl")=some (Rlp.Slices.result array count))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (arena : Rlp.Validation.Arena source cursor limit) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source branchBody=(some (.returned value),target)) :
    count=17#64 ∧ AllocatedBytes.Arena heap 176 ∧ Arenas.Room .down cursor limit 88#64 ∧
      AllocatedBytes.Arena (WitnessRecord.pointer cursor) 88 ∧ Rlp.Validation.Arena target (WitnessRecord.pointer cursor) limit ∧
      ((WitnessRecord.pointer cursor).toNat-limit.toNat)/88+1≤(cursor.toNat-limit.toNat)/88 ∧
      value=.rStruct [.val (.word 1#64),.val (.word (WitnessRecord.pointer cursor))] ∧ 11≤source.clock ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite
        {Arenas.post {branchAllocated source heap with clock:=source.clock-11} .down cursor 88#64 with
          memory:=WordWrites.write (branchAllocated source heap).memory
            (LocalFields.writes (WitnessRecord.pointer cursor) (branchFields (branchWords array pointer length heap)))} := by
  rw [branch_shape] at normal
  obtain ⟨guardRun,branchRun⟩:=Fail.guard_return source target (.cmp .notEqual (field "sl" 1) (.const 17#64)) [.const 4#64]
    (.decCall (ofString "br") .one (ofString "node_new_branch") [] (.decCall (ofString "rec2") .one (ofString "scratch_alloc") [.const 88#64] afterBranchRecord)) value installed normal
  have passed:=(Fail.guard_normal source source _ [.const 4#64] installed guardRun).1
  have test : eval source (.cmp .notEqual (field "sl" 1) (.const 17#64))=some (.val (.word (if count≠17#64 then 1#64 else 0#64))):=by
    simp [eval,field,evalHOLExact,localVar,toExact,sliceCell,Rlp.Slices.result,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have countEq : count=17#64:=by
    by_contra different
    rw [if_pos different] at test
    have impossible : (1#64 : BitVec 64)=0#64:=by
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using test.symm.trans passed
    exact (by decide : (1#64 : BitVec 64)≠0#64) impossible
  have recordShape:=RecordKind.call_shape .branch
  change branchRecord=.decCall (ofString "rec2") .one (ofString "scratch_alloc") [.const 88#64] afterBranchRecord at recordShape
  rw [←recordShape] at branchRun
  obtain ⟨callee,called⟩:=Input.Main.nullary_environment source.code.lookup (ofString "node_new_branch") (NodeConstructor.body .branch)
    (NodeConstructor.original_code .branch source.code installed)
  obtain ⟨funded,built,returned,inner,bodyRun,checked,continued,endpoint⟩:=Input.CallNormal.scoped_normal source target "br" .one (ofString "node_new_branch") [] []
    (NodeConstructor.body .branch) branchRecord callee .one rfl called value branchRun
  obtain ⟨returnedEq,nodeArena,nodeFunding,nodeFrame⟩:=NodeConstructor.branch_normal (callEntryStateHOLFinite source callee) built heap
    arena.domain heapCell heapArena heapAligned installed returned bodyRun
  rw [returnedEq] at continued
  have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) nodeFrame
  change {built with locals:=source.locals}=
    {PersistentAlloc.post {source with clock:=source.clock-1-9} heap 176#64 with memory:=StoreWord.put (Zero.finalMemory source.memory heap 176) heap 3#64} at callerFrame
  rw [Nat.sub_sub] at callerFrame
  change {built with locals:=source.locals}=branchAllocated source heap at callerFrame
  let ready:=bind (branchAllocated source heap) "br" heap
  change evaluateHOLFiniteState (bind {built with locals:=source.locals} "br" heap) branchRecord=(some (.returned value),inner) at continued
  rw [callerFrame] at continued
  have currentArena : Rlp.Validation.Arena ready cursor limit:=by
    refine ⟨arena.domain,?_,?_,arena.ordered,arena.aligned,arena.lower,arena.upper⟩
    · simpa [ready,QueryBranch.bind,setVarHOLFinite,branchAllocated,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,
        show ofString "heap_ptr"≠ofString "scratch_ptr" from by decide] using arena.cursorGlobal
    · simpa [ready,QueryBranch.bind,setVarHOLFinite,branchAllocated,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,
        show ofString "heap_ptr"≠ofString "frame_mem_ptr" from by decide] using arena.limitGlobal
  have currentInstalled : Input.OriginalCode.Installed ready.code:=installed
  have currentArray : ready.locals.lookup (ofString "arr")=some (.val (.word array)):=
    (bind_lookup_other (branchAllocated source heap) "br" "arr" heap (by decide)).trans arrayCell
  have currentPointer : ready.locals.lookup (ofString "p")=some (.val (.word pointer)):=
    (bind_lookup_other (branchAllocated source heap) "br" "p" heap (by decide)).trans pointerCell
  have currentLength : ready.locals.lookup (ofString "n")=some (.val (.word length)):=
    (bind_lookup_other (branchAllocated source heap) "br" "n" heap (by decide)).trans lengthCell
  have currentBranch : ready.locals.lookup (ofString "br")=some (.val (.word heap)):=bind_lookup_same _ _ _
  have recordReady:=branch_record_ready (bind ready "rec2" (WitnessRecord.pointer cursor)) array pointer length heap
    ((bind_lookup_other ready "rec2" "arr" _ (by decide)).trans currentArray)
    ((bind_lookup_other ready "rec2" "p" _ (by decide)).trans currentPointer)
    ((bind_lookup_other ready "rec2" "n" _ (by decide)).trans currentLength)
    ((bind_lookup_other ready "rec2" "br" _ (by decide)).trans currentBranch)
  obtain ⟨room,recordArena,nextArena,recordUpper,decreases,valueEq,recordFunding,recordFrame⟩:=
    record_call_normal .branch ready inner cursor limit (branchWords array pointer length heap) currentArena recordReady currentInstalled value continued
  have finalArena : Rlp.Validation.Arena target (WitnessRecord.pointer cursor) limit:=by
    apply Rlp.Validation.Arena.of_fields inner target _ _ nextArena
    · rw [endpoint]; rfl
    · rw [endpoint]; rfl
  have finalFrame : emptyLocalsHOLFinite target=emptyLocalsHOLFinite
      {Arenas.post {branchAllocated source heap with clock:=source.clock-11} .down cursor 88#64 with
        memory:=WordWrites.write (branchAllocated source heap).memory
          (LocalFields.writes (WitnessRecord.pointer cursor) (branchFields (branchWords array pointer length heap)))}:=by
    rw [endpoint]
    change emptyLocalsHOLFinite inner=_
    rw [recordFrame]
    change emptyLocalsHOLFinite
      {Arenas.post {branchAllocated source heap with clock:=source.clock-10-1} .down cursor 88#64 with
        memory:=WordWrites.write (branchAllocated source heap).memory
          (LocalFields.writes (WitnessRecord.pointer cursor) (branchFields (branchWords array pointer length heap)))}=_
    rw [Nat.sub_sub]
  change 9≤source.clock-1 at nodeFunding
  change 1≤source.clock-10 at recordFunding
  exact ⟨countEq,nodeArena,room,recordArena,finalArena,decreases,valueEq,by omega,finalFrame⟩

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.branch_normal
