import InitECandidate.Solver.Rlp.DecodeNormalFrame

namespace InitECandidate.Solver.Rlp.Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A genuine normal full-decode caller derives the actual complete item,
retained arena, paid clocks and real resumed continuation. -/
theorem scoped_normal_above (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (Header.values pointer length))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) Item.resultShape (ofString "rlp_decode_fully") expressions continuation)=(some (.returned value),post)) :
    1≤source.clock ∧ ∃ calleePost answer inner,Complete pointer length answer ∧ Validation.Arena calleePost cursor limit ∧ Validation.Above source calleePost cursor.toNat ∧
      source.clock-calleePost.clock≤60*length.toNat+44 ∧
      evaluateHOLFiniteState (Input.CallNormal.continuationEntry source calleePost name answer) continuation=(some (.returned value),inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_decode_fully") body Item.resultShape pointer length (original_code source.code installed)
  obtain ⟨positive,calleePost,answer,inner,bodyRun,checked,continuationRun,restored⟩ := Input.CallNormal.scoped_normal source post name Item.resultShape (ofString "rlp_decode_fully") expressions _ body continuation callee Item.resultShape args called value normal
  obtain ⟨complete,nextArena,above,priced⟩ := body_normal_above (callEntryStateHOLFinite source callee) calleePost pointer length cursor limit pointerLocal lengthLocal
    (Validation.Arena.of_fields source _ cursor limit arena rfl rfl) fits installed answer bodyRun
  have clock := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) body
  rw [bodyRun] at clock
  change calleePost.clock≤source.clock-1 at clock
  change source.clock-1-calleePost.clock≤60*length.toNat+43 at priced
  exact ⟨positive,calleePost,answer,inner,complete,nextArena,above,by omega,continuationRun,restored⟩

end InitECandidate.Solver.Rlp.Decode

#print axioms InitECandidate.Solver.Rlp.Decode.scoped_normal_above
