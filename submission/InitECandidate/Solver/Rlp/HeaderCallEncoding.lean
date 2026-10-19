import InitECandidate.Solver.Rlp.HeaderReplay
import InitECandidate.Solver.Rlp.HeaderCallNormal

namespace InitECandidate.Solver.Rlp.Header
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem scoped_normal_encoding (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values pointer length))
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) resultShape (ofString "rlp_item_header") arguments continuation)=(some (.returned returned),post)) :
    ∃ paid header payload flag inner,1≤paid ∧ paid≤11 ∧ paid≤source.clock ∧
      Valid length.toNat (result header payload flag) ∧ Encoded source pointer header payload flag ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString name) (result header payload flag) {source with clock:=source.clock-paid}) continuation=
        (some (.returned returned),inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := environment source.code.lookup pointer length (original_code source.code installed)
  obtain ⟨positive,target,answer,inner,bodyRun,checked,continuationRun,restored⟩ :=
    Input.CallNormal.scoped_normal source post name resultShape (ofString "rlp_item_header") arguments _ body continuation callee resultShape args called returned normal
  obtain ⟨header,payload,flag,encoded,answerEq⟩ := body_encoding (callEntryStateHOLFinite source callee) target pointer pointerLocal installed answer bodyRun
  obtain ⟨paid,minimum,maximum,funded,valid,canonical⟩ := callee_resume source target pointer length callee pointerLocal lengthLocal positive installed answer bodyRun
  rw [canonical name,answerEq] at continuationRun
  rw [answerEq] at valid
  exact ⟨paid,header,payload,flag,inner,minimum,maximum,funded,valid,encoded,continuationRun,restored⟩

end InitECandidate.Solver.Rlp.Header

#print axioms InitECandidate.Solver.Rlp.Header.scoped_normal_encoding
