import InitECandidate.Solver.Rlp.ItemBodyFrame
import InitECandidate.Solver.Input.ClockCostScopedReached

namespace InitECandidate.Solver.Rlp.Item
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem scoped_normal_above (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (Header.values pointer length))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) resultShape (ofString "rlp_item") arguments continuation)=(some (.returned returned),post)) :
    1≤source.clock ∧ ∃ calleePost header payload flag inner,
      Valid pointer length.toNat (result pointer header payload flag) ∧ Validation.Arena calleePost cursor limit ∧
      Validation.Above source calleePost cursor.toNat ∧ calleePost.memaddrs=source.memaddrs ∧ calleePost.be=source.be ∧ calleePost.code=source.code ∧
      calleePost.globals.lookup (ofString "heap_ptr")=source.globals.lookup (ofString "heap_ptr") ∧
      source.clock-calleePost.clock≤60*length.toNat+42 ∧
      evaluateHOLFiniteState (Input.CallNormal.continuationEntry source calleePost name (result pointer header payload flag)) continuation=
        (some (.returned returned),inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_item") body resultShape pointer length (original_code source.code installed)
  obtain ⟨positive,calleePost,answer,inner,bodyRun,checked,continuationRun,restored⟩ :=
    Input.CallNormal.scoped_normal source post name resultShape (ofString "rlp_item") arguments _ body continuation callee resultShape args called returned normal
  obtain ⟨header,payload,flag,answerEq,valid,nextArena,above,domainEq,endianEq,codeEq,heapEq,price⟩ :=
    body_frame (callEntryStateHOLFinite source callee) calleePost pointer length cursor limit pointerLocal lengthLocal
      (Validation.Arena.of_fields source _ cursor limit arena rfl rfl) fits installed answer bodyRun
  rw [answerEq] at continuationRun
  have clock := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) body
  rw [bodyRun] at clock
  change calleePost.clock≤source.clock-1 at clock
  change source.clock-1-calleePost.clock≤60*length.toNat+41 at price
  exact ⟨positive,calleePost,header,payload,flag,inner,valid,nextArena,above,domainEq,endianEq,codeEq,heapEq,by omega,continuationRun,restored⟩

/-- Price only genuine continuations reached by original item returns. The
callee's value, arena, ordinary-memory frame and immutable code/heap facts
are derived before invoking the current continuation bound. -/
theorem scoped_frame_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailPrice : Nat)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (Header.values pointer length))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code)
    (tail : ∀ calleePost header payload flag,
      Valid pointer length.toNat (result pointer header payload flag) → Validation.Arena calleePost cursor limit →
      Validation.Above source calleePost cursor.toNat → calleePost.memaddrs=source.memaddrs → calleePost.be=source.be → calleePost.code=source.code →
      calleePost.globals.lookup (ofString "heap_ptr")=source.globals.lookup (ofString "heap_ptr") →
      let ready:=Input.CallNormal.continuationEntry source calleePost name (result pointer header payload flag)
      ready.clock-(evaluateHOLFiniteState ready continuation).2.clock≤tailPrice) :
    source.clock-(evaluateHOLFiniteState source (.decCall (ofString name) resultShape (ofString "rlp_item") arguments continuation)).2.clock≤60*length.toNat+42+tailPrice := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_item") body resultShape pointer length (original_code source.code installed)
  have entryArena := Validation.Arena.of_fields source (callEntryStateHOLFinite source callee) cursor limit arena rfl rfl
  have priced := Input.ClockCost.scoped_reached_current source name resultShape (ofString "rlp_item") arguments _ body continuation callee resultShape
    (60*length.toNat+41) tailPrice args called
    (body_cost (callEntryStateHOLFinite source callee) pointer length cursor limit pointerLocal lengthLocal entryArena fits installed) ?_
  · omega
  · intro calleePost answer bodyRun checked
    obtain ⟨header,payload,flag,answerEq,valid,nextArena,above,domainEq,endianEq,codeEq,heapEq,price⟩ :=
      body_frame (callEntryStateHOLFinite source callee) calleePost pointer length cursor limit pointerLocal lengthLocal entryArena fits installed answer bodyRun
    rw [answerEq]
    exact tail calleePost header payload flag valid nextArena above domainEq endianEq codeEq heapEq

end InitECandidate.Solver.Rlp.Item

#print axioms InitECandidate.Solver.Rlp.Item.scoped_normal_above
#print axioms InitECandidate.Solver.Rlp.Item.scoped_frame_cost
