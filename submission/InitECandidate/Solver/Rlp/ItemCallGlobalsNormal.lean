import InitECandidate.Solver.Rlp.ItemCallFrame
import InitECandidate.Solver.Rlp.DecodeGlobals

namespace InitECandidate.Solver.Rlp.Item
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Genuine scoped item returns with the complete preserved global map.
The scratch word is restored by the real returned arena; every other
global is preserved by the original helper's checked effects. -/
theorem scoped_normal_globals (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (Header.values pointer length))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) resultShape (ofString "rlp_item") arguments continuation)=(some (.returned returned),post)) :
    1≤source.clock ∧ ∃ calleePost header payload flag inner,
      Valid pointer length.toNat (result pointer header payload flag) ∧ Validation.Arena calleePost cursor limit ∧
      Validation.Above source calleePost cursor.toNat ∧ calleePost.memaddrs=source.memaddrs ∧ calleePost.be=source.be ∧ calleePost.code=source.code ∧
      calleePost.globals.lookup (ofString "heap_ptr")=source.globals.lookup (ofString "heap_ptr") ∧
      (∀ key,calleePost.globals.lookup key=source.globals.lookup key) ∧
      source.clock-calleePost.clock≤60*length.toNat+42 ∧
      evaluateHOLFiniteState (Input.CallNormal.continuationEntry source calleePost name (result pointer header payload flag)) continuation=
        (some (.returned returned),inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩:=Rlp.environment source.code.lookup (ofString "rlp_item") body resultShape pointer length (original_code source.code installed)
  obtain ⟨positive,calleePost,answer,inner,bodyRun,checked,continuationRun,restored⟩:=
    Input.CallNormal.scoped_normal source post name resultShape (ofString "rlp_item") arguments _ body continuation callee resultShape args called returned normal
  obtain ⟨header,payload,flag,answerEq,valid,nextArena,above,domainEq,endianEq,codeEq,heapEq,price⟩:=
    body_frame (callEntryStateHOLFinite source callee) calleePost pointer length cursor limit pointerLocal lengthLocal
      (Validation.Arena.of_fields source _ cursor limit arena rfl rfl) fits installed answer bodyRun
  have globalCells (key : MlS) : calleePost.globals.lookup key=source.globals.lookup key:=by
    by_cases scratch : key=ofString "scratch_ptr"
    · subst key
      exact nextArena.cursorGlobal.trans arena.cursorGlobal.symm
    · have frame:=globals key source.code installed scratch (callEntryStateHOLFinite source callee) rfl
      rw [bodyRun] at frame
      exact congrArg Prod.snd frame
  rw [answerEq] at continuationRun
  have clock:=evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) body
  rw [bodyRun] at clock
  change calleePost.clock≤source.clock-1 at clock
  change source.clock-1-calleePost.clock≤60*length.toNat+41 at price
  exact ⟨positive,calleePost,header,payload,flag,inner,valid,nextArena,above,domainEq,endianEq,codeEq,heapEq,globalCells,by omega,continuationRun,restored⟩

end InitECandidate.Solver.Rlp.Item

#print axioms InitECandidate.Solver.Rlp.Item.scoped_normal_globals
