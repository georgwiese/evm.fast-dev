import InitECandidate.Solver.Rlp.ListCountNormal

namespace InitECandidate.Solver.Rlp.ListCount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Header.values pointer length))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (.call (Input.LocalEffects.callInfo destination) (ofString "rlp_list_count") arguments)).2.clock≤60*length.toNat+32 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_list_count") body .one pointer length (original_code source.code installed)
  exact Input.ClockCost.call_current source destination (ofString "rlp_list_count") arguments _ body callee .one (60*length.toNat+31) args called
    (body_cost (callEntryStateHOLFinite source callee) pointer length cursor limit pointerLocal lengthLocal (Validation.Arena.of_fields source _ cursor limit arena rfl rfl) fits installed)

theorem scoped_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailPrice : Nat)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Header.values pointer length))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (tail : Input.ClockCost.Bound source.code continuation tailPrice) :
    source.clock-(evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "rlp_list_count") arguments continuation)).2.clock≤60*length.toNat+32+tailPrice := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_list_count") body .one pointer length (original_code source.code installed)
  have price := Input.ClockCost.scoped_current source (ofString name) .one (ofString "rlp_list_count") arguments _ body continuation callee .one (60*length.toNat+31) tailPrice args called
    (body_cost (callEntryStateHOLFinite source callee) pointer length cursor limit pointerLocal lengthLocal (Validation.Arena.of_fields source _ cursor limit arena rfl rfl) fits installed) tail
  omega

theorem scoped_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Header.values pointer length))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "rlp_list_count") arguments continuation)=(some (.returned returned),post)) :
    1≤source.clock ∧ ∃ calleePost countWord inner,
      countWord.toNat≤length.toNat ∧ Validation.Arena calleePost cursor limit ∧
      evaluateHOLFiniteState (Input.CallNormal.continuationEntry source calleePost name (.val (.word countWord))) continuation=(some (.returned returned),inner) ∧
      post=WitnessRadix.QueryBranch.restore source name inner := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_list_count") body .one pointer length (original_code source.code installed)
  obtain ⟨positive,calleePost,value,inner,bodyRun,checked,continuationRun,restored⟩ := Input.CallNormal.scoped_normal source post name .one (ofString "rlp_list_count") arguments _ body continuation callee .one args called returned normal
  obtain ⟨countWord,valueEq,bounded,nextArena⟩ := body_normal (callEntryStateHOLFinite source callee) calleePost pointer length cursor limit pointerLocal lengthLocal
    (Validation.Arena.of_fields source _ cursor limit arena rfl rfl) fits installed value bodyRun
  rw [valueEq] at continuationRun
  exact ⟨positive,calleePost,countWord,inner,bounded,nextArena,continuationRun,restored⟩

end InitECandidate.Solver.Rlp.ListCount

#print axioms InitECandidate.Solver.Rlp.ListCount.call_cost
#print axioms InitECandidate.Solver.Rlp.ListCount.scoped_cost
#print axioms InitECandidate.Solver.Rlp.ListCount.scoped_normal
