import InitECandidate.Solver.Rlp.CurrentItem.Memory
import InitECandidate.Solver.Input.ScopedCallNone
import InitECandidate.Solver.Rlp.DecodeGlobals

namespace InitECandidate.Solver.Rlp.Item
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A genuine item call whose enclosing continuation completes normally
retains the complete preserved global map.
The scratch word is restored by the real returned arena; every other
global is preserved by the original helper's checked effects. -/
theorem scoped_none_globals (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (Header.values pointer length))
    (live : LiveArena source) (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) resultShape (ofString "rlp_item") arguments continuation)=(none,post)) :
    1≤source.clock ∧ ∃ calleePost header payload flag inner,
      Valid pointer length.toNat (result pointer header payload flag) ∧ Validation.Arena calleePost cursor limit ∧
      Validation.Above source calleePost cursor.toNat ∧ CurrentItem.Frame source calleePost ∧ calleePost.memaddrs=source.memaddrs ∧ calleePost.be=source.be ∧ calleePost.code=source.code ∧
      calleePost.globals.lookup (ofString "heap_ptr")=source.globals.lookup (ofString "heap_ptr") ∧
      (∀ key,calleePost.globals.lookup key=source.globals.lookup key) ∧
      source.clock-calleePost.clock≤60*length.toNat+11 ∧
      evaluateHOLFiniteState (Input.CallNormal.continuationEntry source calleePost name (result pointer header payload flag)) continuation=
        (none,inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩:=Rlp.environment source.code.lookup (ofString "rlp_item") body resultShape pointer length (original_code source.code installed)
  obtain ⟨positive,calleePost,answer,inner,bodyRun,checked,continuationRun,restored⟩:=
    Input.CallNormal.scoped_none source post name resultShape (ofString "rlp_item") arguments _ body continuation callee resultShape args called normal
  obtain ⟨valid,frame,above,price⟩:=CurrentItem.body_normal_above (callEntryStateHOLFinite source callee) calleePost pointer length cursor limit pointerLocal lengthLocal
    (live.of_frame rfl) (arena.of_fields source _ cursor limit rfl rfl) fits installed answer bodyRun
  have currentFrame : CurrentItem.Frame source calleePost:=frame.of_erase rfl rfl
  have globalEq:=congrArg PanSemStateFiniteExact.globals currentFrame.metadata
  change calleePost.globals=source.globals at globalEq
  have domainEq : calleePost.memaddrs=source.memaddrs:=Input.MemoryMetadata.domain currentFrame.metadata
  have endianEq : calleePost.be=source.be:=Input.MemoryMetadata.endian currentFrame.metadata
  have codeEq : calleePost.code=source.code:=Input.MemoryMetadata.code currentFrame.metadata
  have nextArena:=arena.of_fields source calleePost cursor limit domainEq globalEq
  have globalCells (key : MlS) : calleePost.globals.lookup key=source.globals.lookup key:=by rw [globalEq]
  obtain ⟨header,payload,flag,answerEq,fields⟩:=valid
  have actualValid : Valid pointer length.toNat (result pointer header payload flag):=⟨header,payload,flag,rfl,fields⟩
  rw [answerEq] at continuationRun
  have clock:=evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) body
  rw [bodyRun] at clock
  change calleePost.clock≤source.clock-1 at clock
  change source.clock-1-calleePost.clock≤60*length.toNat+10 at price
  exact ⟨positive,calleePost,header,payload,flag,inner,actualValid,nextArena,above,currentFrame,domainEq,endianEq,codeEq,globalCells _,globalCells,by omega,continuationRun,restored⟩

end InitECandidate.Solver.Rlp.Item

#print axioms InitECandidate.Solver.Rlp.Item.scoped_none_globals
