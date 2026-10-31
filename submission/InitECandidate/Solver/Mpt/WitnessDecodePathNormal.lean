import InitECandidate.Solver.Mpt.WitnessDecodeRows
import InitECandidate.Solver.Mpt.FailGuardReturn
import InitECandidate.Solver.Rlp.CurrentItem.Call
import InitECandidate.Solver.Input.CallResumeLookup

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The real row0 parser reaches its continuation only after the original
string guard. That actual kind-zero return gives a full readonly frame,
including persistent rows below scratch in the current memory layout. -/
theorem path_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array listPointer cursor limit : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem) (pathItem : Rlp.ListItem)
    (rows : Rows source array listPointer bytes items) (selected : items[0]?=some pathItem)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (live : Rlp.LiveArena source) (arena : Rlp.Validation.Arena source cursor limit)
    (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source pairBody=(some (.returned value),post)) :
    ∃ target header payload inner,
      let ready:=CallNormal.continuationEntry source target "pi" (Rlp.Item.result (Rlp.Slices.itemPointer listPointer items 0) header payload 0#64)
      Rlp.Item.Valid (Rlp.Slices.itemPointer listPointer items 0) pathItem.total.toNat (Rlp.Item.result (Rlp.Slices.itemPointer listPointer items 0) header payload 0#64) ∧
      payload.toNat≤bytes ∧ Rows ready array listPointer bytes items ∧ Rlp.Validation.Arena ready cursor limit ∧
      LocalEffects.erase ready=LocalEffects.erase source ∧
      ready.locals.lookup (ofString "arr")=some (.val (.word array)) ∧
      ready.locals.lookup (ofString "pi")=some (Rlp.Item.result (Rlp.Slices.itemPointer listPointer items 0) header payload 0#64) ∧
      evaluateHOLFiniteState ready compactCall=(some (.returned value),inner) ∧ post=restore source "pi" inner := by
  obtain ⟨args,positive,itemBound,lower,upper⟩:=rows.arguments source array listPointer bytes 0 items pathItem selected arrayCell
  have fits : (Rlp.Slices.itemPointer listPointer items 0).toNat+pathItem.total.toNat<2^64:=upper.trans_lt rows.fits
  rw [path_shape] at normal
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩:=Rlp.environment source.code.lookup (ofString "rlp_item")
    Rlp.Item.body Rlp.Item.resultShape (Rlp.Slices.itemPointer listPointer items 0) pathItem.total (Rlp.Item.original_code source.code live.code)
  obtain ⟨funded,target,answer,inner,bodyRun,checked,continued,endpoint⟩:=CallNormal.scoped_normal source post "pi" Rlp.Item.resultShape
    (ofString "rlp_item") (recordArguments 0) _ Rlp.Item.body afterPath callee Rlp.Item.resultShape args called value normal
  obtain ⟨valid,itemFrame,price⟩:=Rlp.CurrentItem.body_normal (callEntryStateHOLFinite source callee) target
    (Rlp.Slices.itemPointer listPointer items 0) pathItem.total pointerLocal lengthLocal (live.of_frame rfl) fits live.code answer bodyRun
  have validity:=valid
  obtain ⟨header,payload,flag,answerEq,headerBound,itemPositive,totalBound,binary,listHeader⟩:=valid
  rw [answerEq] at continued
  let ready:=CallNormal.continuationEntry source target "pi" (Rlp.Item.result (Rlp.Slices.itemPointer listPointer items 0) header payload flag)
  have readyLive : Rlp.LiveArena ready:=live.of_metadata itemFrame.metadata
  have itemCell : ready.locals.lookup (ofString "pi")=some (Rlp.Item.result (Rlp.Slices.itemPointer listPointer items 0) header payload flag):=
    CallNormal.continuation_lookup_same _ _ _ _
  rw [after_path_shape] at continued
  obtain ⟨guardRun,tailRun⟩:=Fail.guard_return ready inner (.cmp .notEqual (field "pi" 0) (.const 0#64)) [.const 5#64] compactCall value readyLive.code continued
  have passed:=(Fail.guard_normal ready ready _ [.const 5#64] readyLive.code guardRun).1
  have flagZero : flag=0#64:=by
    by_contra different
    have test : eval ready (.cmp .notEqual (field "pi" 0) (.const 0#64))=some (.val (.word 1#64)):=by
      simp [eval,field,evalHOLExact,localVar,toExact,itemCell,Rlp.Item.result,different,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have impossible : (1#64 : BitVec 64)=0#64:=by
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using test.symm.trans passed
    exact (by decide : (1#64 : BitVec 64)≠0#64) impossible
  have kind : Rlp.CurrentItem.kindOf answer=some 0#64:=by rw [answerEq,flagZero]; rfl
  have pure:=Rlp.CurrentItem.body_string_frame (callEntryStateHOLFinite source callee) target
    (Rlp.Slices.itemPointer listPointer items 0) pathItem.total pointerLocal lengthLocal (live.of_frame rfl) fits live.code answer kind bodyRun
  have pureReady : LocalEffects.erase ready=LocalEffects.erase source:=pure
  have domain:=congrArg PanSemStateFiniteExact.memaddrs pureReady
  have memory:=LocalEffects.memory_of_erase source ready pureReady
  have globals:=congrArg PanSemStateFiniteExact.globals pureReady
  change ready.globals=source.globals at globals
  have currentRows : Rows ready array listPointer bytes items:=rows.frame source ready array listPointer bytes items domain (by intro query low high; exact congrFun memory query)
  have currentArena:=arena.of_fields source ready cursor limit domain globals
  have currentArray : ready.locals.lookup (ofString "arr")=some (.val (.word array)):=
    (CallNormal.continuation_lookup_other source target "pi" "arr" _ (by decide)).trans arrayCell
  have exactValid : Rlp.Item.Valid (Rlp.Slices.itemPointer listPointer items 0) pathItem.total.toNat (Rlp.Item.result (Rlp.Slices.itemPointer listPointer items 0) header payload flag):=by
    rw [←answerEq]
    exact validity
  subst flag
  exact ⟨target,header,payload,inner,exactValid,by omega,currentRows,currentArena,pureReady,currentArray,itemCell,tailRun,endpoint⟩

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.path_normal
