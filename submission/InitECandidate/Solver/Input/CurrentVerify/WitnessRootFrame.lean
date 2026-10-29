import InitECandidate.Solver.Input.CurrentVerify.WitnessRootCost
import InitECandidate.Solver.Mpt.CurrentWitnessMaterializeOuterFrame
import InitECandidate.Solver.Mpt.CurrentWitnessRootSuffixFrame
import InitECandidate.Solver.Mpt.CurrentWitnessRootNormalTrace

namespace InitECandidate.Solver.Input.CurrentVerify
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch Mpt.WitnessDecodeRoot

/-- The real materializer call and subsequent cache suffix preserve the
original input frontier, using their actual intermediate allocator cursor. -/
theorem witness_materialize_call_normal_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap root : BitVec 64)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root)))
    (recordCell : source.locals.lookup (ofString "r")=some (CurrentTable.NodeLookup.presentValue pointer length))
    (small : length.toNat≤1024) (before : pointer.toNat+length.toNat≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source materializeCall=(some (.returned value),post)) :
    ∃ node,value=.val (.word node) ∧ (node=0#64 ∨ heap.toNat≤node.toNat ∧ node.toNat≤2952790016) ∧ PersistentNormalFrame source post heap := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) materializeArguments=
      some [.val (.word db),.val (.word pointer),.val (.word length)] := by
    simp [materializeArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,dbCell,recordCell,CurrentTable.NodeLookup.presentValue]
  obtain ⟨callee,called,dbLocal,pointerLocal,lengthLocal⟩:=word_triple_environment source.code.lookup
    (ofString "_decode_witness_node") (ofString "db") (ofString "p") (ofString "n") Mpt.WitnessMaterialize.body .one
    db pointer length (by decide) (by decide) (by decide) (Mpt.WitnessMaterialize.original_code source.code arena.code)
  rw [lookup_tail_shape.2] at normal
  obtain ⟨funded,target,answer,inner,bodyRun,checked,continued,endpoint⟩:=CallNormal.scoped_normal source post "nd" .one (ofString "_decode_witness_node")
    materializeArguments _ Mpt.WitnessMaterialize.body afterMaterialize callee .one args called value normal
  obtain ⟨node,answerEq,bounds,bodyFrame⟩:=Mpt.WitnessMaterialize.current_body_normal_frame (callEntryStateHOLFinite source callee) target db pointer length heap
    dbLocal pointerLocal lengthLocal small before heapCell heapArena heapBound aligned (arena.of_frame rfl) answer bodyRun
  rw [answerEq] at continued
  let ready:=CallNormal.continuationEntry source target "nd" (.val (.word node))
  have frame : PersistentNormalFrame source ready heap:=bodyFrame.of_erase _ _ source ready heap rfl rfl
  obtain ⟨next,nextCell,nextArena,nextBound,nextAligned,grows⟩:=frame.nextHeap
  have currentRoot : ready.locals.lookup (ofString "root_hash")=some (.val (.word root)):=
    (CallNormal.continuation_lookup_other source target "nd" "root_hash" _ (by decide)).trans rootCell
  have nodeCell : ready.locals.lookup (ofString "nd")=some (.val (.word node)):=CallNormal.continuation_lookup_same _ _ _ _
  obtain ⟨valueEq,tailFrame⟩:=current_suffix_normal_frame ready inner next heap root node currentRoot nodeCell grows bounds
    nextCell nextArena nextBound nextAligned (frame.current_arena arena) value continued
  have total:=frame.trans source ready inner heap heap tailFrame (Nat.le_refl _)
  exact ⟨node,valueEq,bounds,total.of_erase source inner source post heap rfl (by rw [endpoint]; rfl)⟩

theorem witness_after_lookup_normal_frame (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (inputPointer db root heap : BitVec 64) (start length boundary : Nat) (answer : ValueHOL 64)
    (result : LookupResult input inputPointer start length boundary 1024 answer)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root)))
    (recordCell : source.locals.lookup (ofString "r")=some answer)
    (before : boundary≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterLookup=(some (.returned value),post)) :
    ∃ node,value=.val (.word node) ∧ (node=0#64 ∨ heap.toNat≤node.toNat ∧ node.toNat≤2952790016) ∧ PersistentNormalFrame source post heap := by
  rcases result with absent|⟨index,inside,present,allocated,lower,extent,small⟩
  · rw [absent] at recordCell
    have guardRun : evaluateHOLFiniteState source missingGuard=evaluateHOLFiniteState source missingCall := by
      simp [missingGuard,missingTest,evaluateHOLFiniteState_ite,evalHOLExact,localVar,recordCell,CurrentTable.NodeLookup.absentValue,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have stops : (evaluateHOLFiniteState source missingGuard).1≠none:=by
      rw [guardRun]
      exact fun normal=>Mpt.Fail.call_not_normal source _ arena.code [.const 1#64] (Prod.ext normal rfl)
    rw [lookup_tail_shape.1,sequence_stopped source missingGuard materializeCall stops,guardRun] at normal
    exact (NoReturn.ignored_call (ofString "mpt_fail") [.const 1#64] source value (congrArg Prod.fst normal)).elim
  · rw [present] at recordCell
    have guardRun : evaluateHOLFiniteState source missingGuard=(none,source) := by
      simp [missingGuard,missingTest,evaluateHOLFiniteState_ite,evalHOLExact,localVar,recordCell,CurrentTable.NodeLookup.presentValue,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
    rw [lookup_tail_shape.1,evaluateHOLFiniteState_seq_line780,guardRun] at normal
    exact witness_materialize_call_normal_frame source post db _ _ heap root dbCell rootCell recordCell small (by omega)
      heapCell heapArena heapBound aligned arena value normal

/-- Whole unchanged current239 normal return with its real matching
witness/table images: returned node bounds, restored scratch, advanced bounded
heap, complete runtime metadata and every earlier input word. -/
theorem witness_root_normal_frame {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si array table cap root heap : BitVec 64} {start length boundary : Nat}
    (witness : CurrentStartup.WitnessArrays.Image input source pointer si array start length boundary 40 1024 (2^31))
    (tableImage : CurrentTable.NodeBuild.ImageUpTo
      {databaseData input array pointer start length boundary 1024 with table:=table,cap:=cap} source (VarList.decodedCount input start length))
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word table)))
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root)))
    (before : boundary≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ node,value=.val (.word node) ∧ (node=0#64 ∨ heap.toNat≤node.toNat ∧ node.toNat≤2952790016) ∧ PersistentNormalFrame source post heap := by
  rcases current_lookup_normal_trace_any source post table root arena.code dbCell rootCell value normal with empty|reached
  · obtain ⟨valueEq,physical⟩:=empty
    exact ⟨0#64,valueEq,Or.inl rfl,(PersistentNormalFrame.refl source heap heapCell heapArena heapBound aligned).of_erase source source source post heap rfl physical⟩
  · obtain ⟨lookupSource,lookupPost,frame,lookupDb,lookupRoot,lookupRun,endpoint⟩:=reached
    obtain ⟨imageRoot,next,count,valid,bits,left,right,keys,image,countBound⟩:=tableImage
    have nextTable : CurrentTable.NodeBuild.ImageUpTo
        {databaseData input array pointer start length boundary 1024 with table:=table,cap:=cap} lookupSource (VarList.decodedCount input start length) :=
      ⟨imageRoot,next,count,valid,bits,left,right,keys,image.of_frame frame,countBound⟩
    have nextWitness:=witness.of_interval (by decide) (by intro query lower before; exact congrFun (LocalEffects.memory_of_erase source lookupSource frame) query)
    have lookupArena:=arena.of_frame frame
    have args : evalListHOLFinite lookupSource (h:=fun query=>Classical.propDecidable (lookupSource.memaddrs query)) lookupArguments=
        some [.val (.word table),.val (.word root)] := by
      simp [lookupArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,lookupDb,lookupRoot]
    rw [shapes.2.2] at lookupRun
    rcases database_lookup_trace_image nextWitness lookupArena.code nextTable (by decide) "r" lookupArguments afterLookup args _ lookupRun with stopped|resumed
    · exact (stopped.2 value rfl).elim
    · obtain ⟨target,answer,inner,result,pure,forward,price,continued,restored⟩:=resumed
      let current:=CallNormal.continuationEntry lookupSource target "r" answer
      have currentFrame : LocalEffects.erase current=LocalEffects.erase source:=pure.trans frame
      have currentDb : current.locals.lookup (ofString "db")=some (.val (.word table)):=
        (CallNormal.continuation_lookup_other lookupSource target "r" "db" answer (by decide)).trans lookupDb
      have currentRoot : current.locals.lookup (ofString "root_hash")=some (.val (.word root)):=
        (CallNormal.continuation_lookup_other lookupSource target "r" "root_hash" answer (by decide)).trans lookupRoot
      have globals:=congrArg PanSemStateFiniteExact.globals currentFrame
      change current.globals=source.globals at globals
      have currentHeap : current.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by rw [globals]; exact heapCell
      obtain ⟨node,valueEq,bounds,tailFrame⟩:=witness_after_lookup_normal_frame input current inner pointer table root heap start length boundary answer result
        currentDb currentRoot (CallNormal.continuation_lookup_same _ _ _ _) before currentHeap heapArena heapBound aligned (arena.of_frame currentFrame) value continued
      have physical : LocalEffects.erase post=LocalEffects.erase inner:=by rw [endpoint,restored]; rfl
      exact ⟨node,valueEq,bounds,tailFrame.of_erase current inner source post heap currentFrame.symm physical⟩

end InitECandidate.Solver.Input.CurrentVerify

#print axioms InitECandidate.Solver.Input.CurrentVerify.witness_materialize_call_normal_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.witness_after_lookup_normal_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.witness_root_normal_frame
