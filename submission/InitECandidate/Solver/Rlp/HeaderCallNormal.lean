import InitECandidate.Solver.Rlp.HeaderNormal
import InitECandidate.Solver.Input.ScopedCallNone

namespace InitECandidate.Solver.Rlp.Header
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem callee_resume (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (pointerLocal : callee.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthLocal : callee.lookup (ofString "len")=some (.val (.word length)))
    (positive : 1≤source.clock) (installed : Input.OriginalCode.Installed source.code) (answer : ValueHOL 64)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(some (.returned answer),target)) :
    ∃ paid,1≤paid ∧ paid≤11 ∧ paid≤source.clock ∧ Valid length.toNat answer ∧
      ∀ name,Input.CallNormal.continuationEntry source target name answer=
        setVarHOLFinite (ofString name) answer {source with clock := source.clock-paid} := by
  obtain ⟨valid,upper,lower,fields⟩ := body_normal (callEntryStateHOLFinite source callee) target pointer length pointerLocal lengthLocal installed answer run
  change target.clock≤source.clock-1 at upper
  change source.clock-1-10≤target.clock at lower
  let paid := source.clock-target.clock
  have clock : source.clock-paid=target.clock := by dsimp [paid]; omega
  refine ⟨paid,by dsimp [paid]; omega,by dsimp [paid]; omega,Nat.sub_le _ _,valid,?_⟩
  intro name
  have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals,clock := target.clock}) fields
  change {target with locals := source.locals}={source with clock := target.clock} at callerFrame
  unfold Input.CallNormal.continuationEntry
  rw [callerFrame,clock]

/-- A real continuing caller gets the actual validated header and an exact
caller state with only its clock and new binding changed. -/
theorem scoped_none (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments=some (values pointer length))
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) resultShape (ofString "rlp_item_header") arguments continuation)=(none,post)) :
    ∃ paid answer inner,1≤paid ∧ paid≤11 ∧ paid≤source.clock ∧ Valid length.toNat answer ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString name) answer {source with clock := source.clock-paid}) continuation=(none,inner) ∧
      post=restore source name inner := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := environment source.code.lookup pointer length (original_code source.code installed)
  obtain ⟨positive,target,answer,inner,bodyRun,checked,continuationRun,restored⟩ :=
    Input.CallNormal.scoped_none source post name resultShape (ofString "rlp_item_header") arguments _ body continuation callee resultShape args called normal
  obtain ⟨paid,minimum,maximum,funded,valid,canonical⟩ := callee_resume source target pointer length callee pointerLocal lengthLocal positive installed answer bodyRun
  rw [canonical name] at continuationRun
  exact ⟨paid,answer,inner,minimum,maximum,funded,valid,continuationRun,restored⟩

theorem scoped_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments=some (values pointer length))
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) resultShape (ofString "rlp_item_header") arguments continuation)=(some (.returned returned),post)) :
    ∃ paid answer inner,1≤paid ∧ paid≤11 ∧ paid≤source.clock ∧ Valid length.toNat answer ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString name) answer {source with clock := source.clock-paid}) continuation=(some (.returned returned),inner) ∧
      post=restore source name inner := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := environment source.code.lookup pointer length (original_code source.code installed)
  obtain ⟨positive,target,answer,inner,bodyRun,checked,continuationRun,restored⟩ :=
    Input.CallNormal.scoped_normal source post name resultShape (ofString "rlp_item_header") arguments _ body continuation callee resultShape args called returned normal
  obtain ⟨paid,minimum,maximum,funded,valid,canonical⟩ := callee_resume source target pointer length callee pointerLocal lengthLocal positive installed answer bodyRun
  rw [canonical name] at continuationRun
  exact ⟨paid,answer,inner,minimum,maximum,funded,valid,continuationRun,restored⟩

end InitECandidate.Solver.Rlp.Header

#print axioms InitECandidate.Solver.Rlp.Header.callee_resume
#print axioms InitECandidate.Solver.Rlp.Header.scoped_none
#print axioms InitECandidate.Solver.Rlp.Header.scoped_normal
