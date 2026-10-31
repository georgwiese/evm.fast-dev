import InitECandidate.Solver.Mpt.WitnessCoreStackPush
import InitECandidate.Solver.Mpt.WitnessCoreResultNode
import InitECandidate.Solver.Input.CoreDecodeNormal
import InitECandidate.Solver.Mpt.WitnessCoreDecodeScope
import InitECandidate.Solver.Mpt.WitnessCoreLoopFields

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Physical alternatives of one genuine decode-mode iteration. Both
derive the actual next heap and scratch; their real locals select the
next phase and their physical stack pays the corresponding rank change. -/
inductive DecodeStep (post : PanSemStateFiniteExact 64 Guest.HostMemory) (db heap cursor limit : BitVec 64) (stack : List Entry) : Prop where
  | terminal (next node : BitVec 64)
      (heapCell : post.globals.lookup (ofString "heap_ptr")=some (.val (.word next)))
      (heapArena : AllocatedBytes.Arena next 0) (aligned : next.toNat%8=0) (grows : heap.toNat≤next.toNat)
      (scratch : Rlp.Validation.Arena post cursor limit) (view : View post db cursor.toNat next.toNat stack)
      (topCell : post.locals.lookup (ofString "top")=some (.val (.word (top stack))))
      (resultCell : post.locals.lookup (ofString "result")=some (.val (.word node)))
      (modeCell : post.locals.lookup (ofString "mode")=some (.val (.word 0#64)))
      (owned : ResultOwned post heap.toNat next.toNat node)
      (decoded : ∃ pointer length,WitnessDecode.NormalResult post db pointer length heap cursor limit (.rStruct [.val (.word 0#64),.val (.word node)]))
      (rank : WitnessStackRank.rank (WitnessStackRank.recordsLeft cursor.toNat limit.toNat) (frames stack) .returning true<
        WitnessStackRank.rank (WitnessStackRank.recordsLeft cursor.toNat limit.toNat) (frames stack) .decode true) : DecodeStep post db heap cursor limit stack
  | pushed (data : WitnessRecord.Description) (next : BitVec 64)
      (heapCell : post.globals.lookup (ofString "heap_ptr")=some (.val (.word next)))
      (heapArena : AllocatedBytes.Arena next 0) (aligned : next.toNat%8=0) (grows : heap.toNat≤next.toNat)
      (scratch : Rlp.Validation.Arena post (WitnessRecord.pointer cursor) limit)
      (view : View post db (WitnessRecord.pointer cursor).toNat next.toNat (⟨WitnessRecord.pointer cursor,data,next.toNat,none⟩::stack))
      (fresh : data.payload.Fresh) (initial : data.payload.InitialValue post)
      (freshRows : heap.toNat≤data.array.toNat) (freshPayload : heap.toNat≤data.payload.startAddress)
      (topCell : post.locals.lookup (ofString "top")=some (.val (.word (WitnessRecord.pointer cursor))))
      (slotCell : post.locals.lookup (ofString "slot")=some (.val (.word (BitVec.ofNat 64 data.payload.slotIndex))))
      (modeCell : post.locals.lookup (ofString "mode")=some (.val (.word 2#64)))
      (rank : WitnessStackRank.rank (WitnessStackRank.recordsLeft (WitnessRecord.pointer cursor).toNat limit.toNat)
        (frames (⟨WitnessRecord.pointer cursor,data,next.toNat,none⟩::stack)) .resolve true<
        WitnessStackRank.rank (WitnessStackRank.recordsLeft cursor.toNat limit.toNat) (frames stack) .decode true) : DecodeStep post db heap cursor limit stack

theorem fresh_slot_of_stage (first second : WitnessRecord.Payload) (freshFirst : first.Fresh) (freshSecond : second.Fresh)
    (same : first.stage=second.stage) : first.slotIndex=second.slotIndex := by
  cases first with
  | extension nibbles length=>
    cases second with
    | extension nibbles' length'=>rfl
    | branch node index occupied=>simp [WitnessRecord.Payload.stage] at same
  | branch node index occupied=>
    cases second with
    | extension nibbles' length'=>simp [WitnessRecord.Payload.stage] at same
    | branch node' index' occupied'=>simp only [WitnessRecord.Payload.slotIndex,freshFirst.1,freshSecond.1]

end InitECandidate.Solver.Mpt.WitnessCore.Stack

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Mpt.WitnessCore Mpt.WitnessCore.Stack

/-- Whole original decode mode advances the physical active stack or
delivers a null/fresh owned result, preserving db/go and decreasing the
real materializer potential. All heap/scratch/results/PREV facts follow
from the same genuine normal execution of the unchanged decode branch. -/
theorem core_decode_stack_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap cursor limit oldResult oldSlot oldMode : BitVec 64) (stack : List Mpt.WitnessCore.Stack.Entry)
    (view : View source db cursor.toNat heap.toNat stack)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "cur_p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "cur_n")=some (.val (.word length)))
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word (top stack))))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word oldResult)))
    (slotCell : source.locals.lookup (ofString "slot")=some (.val (.word oldSlot)))
    (modeCell : source.locals.lookup (ofString "mode")=some (.val (.word oldMode)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (heapAligned : heap.toNat%8=0)
    (live : Rlp.LiveArena source) (arena : Rlp.Validation.Arena source cursor limit)
    (dbBefore : db.toNat≤heap.toNat)
    (before : pointer.toNat+length.toNat≤db.toNat) (small : length.toNat≤1024)
    (inputLower : 2701131776≤pointer.toNat)
    (normal : evaluateHOLFiniteState source decodeBranch=(none,post)) :
    Mpt.WitnessDecode.LiveFrame source post heap cursor limit ∧ DecodeStep post db heap cursor limit stack ∧
      post.locals.lookup (ofString "db")=source.locals.lookup (ofString "db") ∧
      post.locals.lookup (ofString "go")=source.locals.lookup (ofString "go") ∧ DataWords post := by
  obtain ⟨built,returned,frame,result,shape⟩:=core_decode_normal source post db pointer length heap cursor limit (top stack) oldResult oldSlot oldMode
    dbCell pointerCell lengthCell topCell resultCell slotCell modeCell heapCell heapArena heapBound heapAligned live arena dbBefore before small inputLower normal
  let ready:=CallNormal.continuationEntry source built "d" returned
  rcases shape with ⟨node,valueEq,postEq⟩|⟨shapeData,valueEq,shapeFresh,shapeView,postEq⟩
  · rw [valueEq] at result
    obtain ⟨next,nextCell,nextArena,nextBound,aligned,grows⟩:=frame.nextHeap
    have scratch : Rlp.Validation.Arena post cursor limit:=by
      cases result with
      | empty scratch=>exact scratch
      | leaf node nibbles nibbleLength valuePointer valueLength actualHeap leafView freshPath freshNode scratch actualCell heapArena heapAligned nodeBefore=>exact scratch
    have postView:=view.frame source post db cursor.toNat heap.toNat cursor.toNat next.toNat stack (Nat.le_refl _) grows frame.domain frame.memory
    have owned:=decode_result_owned post db pointer length heap cursor limit node next result nextCell
    have fields:=decode_scoped_terminal_fields source ready node
    have postTop : post.locals.lookup (ofString "top")=some (.val (.word (top stack))):=by
      rw [postEq]
      exact (decode_scoped_terminal_other source ready node "top" (by decide) (by decide) (by decide)).trans
        ((CallNormal.continuation_lookup_other source built "d" "top" returned (by decide)).trans topCell)
    have preserved (name : String) (notD : ofString "d"≠ofString name) (notResult : ofString "result"≠ofString name) (notMode : ofString "mode"≠ofString name) :
        post.locals.lookup (ofString name)=source.locals.lookup (ofString name):=by
      rw [postEq]
      exact (decode_scoped_terminal_other source ready node name notD notResult notMode).trans
        (CallNormal.continuation_lookup_other source built "d" name returned notD)
    have postResult : post.locals.lookup (ofString "result")=some (.val (.word node)):=by rw [postEq]; exact fields.1
    have postMode : post.locals.lookup (ofString "mode")=some (.val (.word 0#64)):=by rw [postEq]; exact fields.2.1
    exact ⟨frame,.terminal next node nextCell nextArena aligned grows scratch postView postTop postResult postMode owned ⟨pointer,length,result⟩
      (Mpt.WitnessStackRank.terminal _ _),preserved "db" (by decide) (by decide) (by decide),preserved "go" (by decide) (by decide) (by decide),
      ⟨⟨pointer,(preserved "cur_p" (by decide) (by decide) (by decide)).trans pointerCell⟩,
        ⟨length,(preserved "cur_n" (by decide) (by decide) (by decide)).trans lengthCell⟩,
        ⟨node,postResult⟩,⟨oldSlot,(preserved "slot" (by decide) (by decide) (by decide)).trans slotCell⟩⟩⟩
  · rw [valueEq] at result
    have fields:=decode_scoped_push_fields source ready (Mpt.WitnessRecord.pointer cursor) (top stack) shapeData.payload shapeFresh
    have link : post.memory (Mpt.WitnessRecord.pointer cursor)=.word (top stack):=by rw [postEq]; exact fields.2.2.2.1
    obtain ⟨data,next,postView,fresh,initial,parentPointer,parentLength,nextCell,nextArena,aligned,scratch,grows,freshRows,freshPayload,rank⟩:=
      push_record_result source post db pointer length heap cursor limit stack view arena frame result link
    let entry : Mpt.WitnessCore.Stack.Entry:=⟨Mpt.WitnessRecord.pointer cursor,data,next.toNat,none⟩
    have recordView:=postView.records entry List.mem_cons_self
    have stageEq : data.payload.stage=shapeData.payload.stage:=HolWordLab.word.inj
      ((recordView.stage post _ db data).symm.trans (shapeView.stage post _ db shapeData))
    have slotEq:=fresh_slot_of_stage shapeData.payload data.payload shapeFresh fresh stageEq.symm
    have postTop : post.locals.lookup (ofString "top")=some (.val (.word (Mpt.WitnessRecord.pointer cursor))):=by rw [postEq]; exact fields.1
    have postSlot : post.locals.lookup (ofString "slot")=some (.val (.word (BitVec.ofNat 64 data.payload.slotIndex))):=by rw [postEq,←slotEq]; exact fields.2.1
    have postMode : post.locals.lookup (ofString "mode")=some (.val (.word 2#64)):=by rw [postEq]; exact fields.2.2.1
    have preserved (name : String) (notD : ofString "d"≠ofString name) (notTop : ofString "top"≠ofString name)
        (notSlot : ofString "slot"≠ofString name) (notMode : ofString "mode"≠ofString name) : post.locals.lookup (ofString name)=source.locals.lookup (ofString name):=by
      rw [postEq]
      exact (decode_scoped_push_other source ready _ (top stack) shapeData.payload name notD notTop notSlot notMode).trans
        (CallNormal.continuation_lookup_other source built "d" name returned notD)
    exact ⟨frame,.pushed data next nextCell nextArena aligned grows scratch postView fresh initial freshRows freshPayload postTop postSlot postMode rank,
      preserved "db" (by decide) (by decide) (by decide) (by decide),preserved "go" (by decide) (by decide) (by decide) (by decide),
      ⟨⟨pointer,(preserved "cur_p" (by decide) (by decide) (by decide) (by decide)).trans pointerCell⟩,
        ⟨length,(preserved "cur_n" (by decide) (by decide) (by decide) (by decide)).trans lengthCell⟩,
        ⟨oldResult,(preserved "result" (by decide) (by decide) (by decide) (by decide)).trans resultCell⟩,⟨_,postSlot⟩⟩⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.fresh_slot_of_stage
#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.core_decode_stack_normal
