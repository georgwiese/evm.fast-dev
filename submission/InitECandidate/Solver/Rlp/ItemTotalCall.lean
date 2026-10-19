import InitECandidate.Solver.Rlp.ItemTotalNormal
import InitECandidate.Solver.Input.ClockCostCurrentScoped

namespace InitECandidate.Solver.Rlp.ItemTotal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem scoped_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Header.values pointer length))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code)
    (quiet : Input.ClockCost.Bound source.code continuation 0) :
    source.clock-(evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "rlp_item_total") arguments continuation)).2.clock≤28*length.toNat+31 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_item_total") body .one pointer length (original_code source.code installed)
  exact Input.ClockCost.scoped_current source (ofString name) .one (ofString "rlp_item_total") arguments _ body continuation callee .one (28*length.toNat+30) 0 args called
    (body_cost (callEntryStateHOLFinite source callee) pointer length cursor limit pointerLocal lengthLocal (Validation.Arena.of_fields source _ cursor limit arena rfl rfl) fits installed) quiet

/-- The real scoped caller derives its actual positive size, retained arena,
genuine continuation and caller-plus-callee price<=59*actual item bytes. -/
theorem scoped_none (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Header.values pointer length))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "rlp_item_total") arguments continuation)=(none,post)) :
    1≤source.clock ∧ ∃ calleePost totalWord inner,
      1≤totalWord.toNat ∧ totalWord.toNat≤length.toNat ∧ Validation.Arena calleePost cursor limit ∧
      source.clock-calleePost.clock≤59*totalWord.toNat ∧
      evaluateHOLFiniteState (bind {calleePost with locals:=source.locals} name totalWord) continuation=(none,inner) ∧
      post=restore source name inner := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_item_total") body .one pointer length (original_code source.code installed)
  obtain ⟨positive,calleePost,value,inner,bodyRun,checked,continuationRun,restored⟩ := Input.CallNormal.scoped_none source post name .one (ofString "rlp_item_total") arguments _ body continuation callee .one args called normal
  obtain ⟨totalWord,valueEq,advances,bounded,nextArena,price⟩ := body_normal (callEntryStateHOLFinite source callee) calleePost pointer length cursor limit pointerLocal lengthLocal
    (Validation.Arena.of_fields source _ cursor limit arena rfl rfl) fits installed value bodyRun
  rw [valueEq] at continuationRun
  have clock := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) body
  rw [bodyRun] at clock
  change calleePost.clock≤source.clock-1 at clock
  change source.clock-1-calleePost.clock≤28*totalWord.toNat+30 at price
  exact ⟨positive,calleePost,totalWord,inner,advances,bounded,nextArena,by omega,continuationRun,restored⟩

end InitECandidate.Solver.Rlp.ItemTotal

#print axioms InitECandidate.Solver.Rlp.ItemTotal.scoped_cost
#print axioms InitECandidate.Solver.Rlp.ItemTotal.scoped_none
