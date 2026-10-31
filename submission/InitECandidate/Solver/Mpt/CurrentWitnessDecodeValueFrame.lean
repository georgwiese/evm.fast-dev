import InitECandidate.Solver.Mpt.WitnessDecodeNormalFrame
import InitECandidate.Solver.Mpt.CurrentWitnessDecodeLeafFrame
import InitECandidate.Solver.Mpt.FailGuardReturn

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The actual second-item parse is readonly before its genuine leaf
allocation and stores. The entire leaf path protects the entering frontier. -/
theorem current_leaf_body_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer heap parentPointer parentLength nibbles nibbleLength leaf : BitVec 64)
    (bytes : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (rows : Rows source array pointer bytes items) (selected : items[1]?=some item)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word parentPointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word parentLength)))
    (compactCell : source.locals.lookup (ofString "cn")=some (.rStruct [.val (.word nibbles),.val (.word nibbleLength),.val (.word leaf)]))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : Rlp.LiveArena source) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source leafBody=(some (.returned value),post)) :
    value=.rStruct [.val (.word 0#64),.val (.word heap)] ∧ PersistentNormalFrame source post heap ∧
      heap.toNat+64≤2952790016 ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat ∨ heap.toNat+64≤query.toNat→post.memory query=source.memory query) := by
  obtain ⟨args,positive,small,lower,upper⟩:=rows.arguments source array pointer bytes 1 items item selected arrayCell
  have fits : (Rlp.Slices.itemPointer pointer items 1).toNat+item.total.toNat<2^64:=by have h:=rows.fits; omega
  rw [value_shape] at normal
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩:=Rlp.environment source.code.lookup (ofString "rlp_item")
    Rlp.Item.body Rlp.Item.resultShape (Rlp.Slices.itemPointer pointer items 1) item.total (Rlp.Item.original_code source.code arena.code)
  obtain ⟨funded,itemPost,answer,inner,bodyRun,checked,continued,endpoint⟩:=CallNormal.scoped_normal source post "vi" Rlp.Item.resultShape
    (ofString "rlp_item") (recordArguments 1) _ Rlp.Item.body afterValue callee Rlp.Item.resultShape args called value normal
  obtain ⟨valid,itemFrame,price⟩:=Rlp.CurrentItem.body_normal (callEntryStateHOLFinite source callee) itemPost
    (Rlp.Slices.itemPointer pointer items 1) item.total pointerLocal lengthLocal (arena.of_frame rfl) fits arena.code answer bodyRun
  obtain ⟨header,payload,flag,answerEq,headerBound,itemPositive,itemBound,binary,listHeader⟩:=valid
  let ready:=CallNormal.continuationEntry source itemPost "vi" answer
  have currentPointer : ready.locals.lookup (ofString "p")=some (.val (.word parentPointer)) :=
    (CallNormal.continuation_lookup_other source itemPost "vi" "p" _ (by decide)).trans pointerCell
  have currentLength : ready.locals.lookup (ofString "n")=some (.val (.word parentLength)) :=
    (CallNormal.continuation_lookup_other source itemPost "vi" "n" _ (by decide)).trans lengthCell
  have currentCompact : ready.locals.lookup (ofString "cn")=some (.rStruct [.val (.word nibbles),.val (.word nibbleLength),.val (.word leaf)]) :=
    (CallNormal.continuation_lookup_other source itemPost "vi" "cn" _ (by decide)).trans compactCell
  have valueCell : ready.locals.lookup (ofString "vi")=some (Rlp.Item.result (Rlp.Slices.itemPointer pointer items 1) header payload flag) := by
    have actualCell : ready.locals.lookup (ofString "vi")=some answer:=CallNormal.continuation_lookup_same source itemPost "vi" answer
    exact actualCell.trans (congrArg some answerEq)
  have readyArena : Rlp.LiveArena ready:=arena.of_metadata itemFrame.metadata
  rw [after_value_shape] at continued
  obtain ⟨guardRun,actual⟩:=Fail.guard_return ready inner (.cmp .notEqual (field "vi" 0) (.const 0#64)) [.const 6#64] leafAllocate value readyArena.code continued
  have passed:=(Fail.guard_normal ready ready _ [.const 6#64] readyArena.code guardRun).1
  have flagZero : flag=0#64 := by
    by_contra different
    have read : eval ready (.cmp .notEqual (field "vi" 0) (.const 0#64))=some (.val (.word 1#64)) := by
      simp [eval,field,evalHOLExact,localVar,toExact,valueCell,Rlp.Item.result,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,different]
    have impossible : (1#64 : BitVec 64)=0#64 := by
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans passed
    exact (by decide : (1#64 : BitVec 64)≠0#64) impossible
  have stringKind : Rlp.CurrentItem.kindOf answer=some 0#64 := by rw [answerEq,flagZero]; rfl
  have pure:=Rlp.CurrentItem.body_string_frame (callEntryStateHOLFinite source callee) itemPost
    (Rlp.Slices.itemPointer pointer items 1) item.total pointerLocal lengthLocal (arena.of_frame rfl) fits arena.code answer stringKind bodyRun
  have pureReady : LocalEffects.erase ready=LocalEffects.erase source:=pure
  have globals:=congrArg PanSemStateFiniteExact.globals pureReady
  change ready.globals=source.globals at globals
  have readyHeap : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by rw [globals]; exact heapCell
  obtain ⟨valueEq,frame,room,window⟩:=current_leaf_allocate_frame ready inner parentPointer parentLength nibbles nibbleLength leaf flag
    (Rlp.Slices.itemPointer pointer items 1+header) payload (header+payload) heap currentPointer currentLength currentCompact valueCell
    readyHeap heapArena heapBound aligned readyArena value actual
  refine ⟨valueEq,frame.of_erase ready inner source post heap pureReady.symm (by rw [endpoint]; rfl),room,?_⟩
  have memory:=LocalEffects.memory_of_erase source ready pureReady
  intro query outside
  rw [endpoint]
  exact (window query outside).trans (congrFun memory query)

/-- The actual finished-leaf path supplies the same live state frame as
pending records, while retaining its exact returned node and bounded extent. -/
theorem current_leaf_body_live_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer heap parentPointer parentLength nibbles nibbleLength leaf cursor limit : BitVec 64)
    (bytes : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (rows : Rows source array pointer bytes items) (selected : items[1]?=some item)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word parentPointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word parentLength)))
    (compactCell : source.locals.lookup (ofString "cn")=some (.rStruct [.val (.word nibbles),.val (.word nibbleLength),.val (.word leaf)]))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : Rlp.LiveArena source) (physical : Rlp.Validation.Arena source cursor limit)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source leafBody=(some (.returned value),post)) :
    value=.rStruct [.val (.word 0#64),.val (.word heap)] ∧ heap.toNat+64≤2952790016 ∧
      LiveFrame source post heap cursor limit := by
  obtain ⟨answer,persistent,room,window⟩:=current_leaf_body_frame source post array pointer heap parentPointer parentLength nibbles nibbleLength leaf
    bytes items item rows selected arrayCell pointerCell lengthCell compactCell heapCell heapArena heapBound aligned arena value normal
  have above : Rlp.Validation.Above source post cursor.toNat := by
    intro query beyond
    obtain ⟨lower,upper⟩:=arena.bounds physical
    apply window query (Or.inr ?_)
    have ordered:=physical.ordered
    omega
  exact ⟨answer,room,LiveFrame.of_persistent source post heap cursor limit arena physical persistent above⟩

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_leaf_body_frame

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_leaf_body_live_frame
