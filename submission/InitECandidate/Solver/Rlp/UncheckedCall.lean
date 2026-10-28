import InitECandidate.Solver.Rlp.UncheckedEncoding
import InitECandidate.Solver.Rlp.UncheckedCost
import InitECandidate.Solver.Input.LocalEffectsScoped
import InitECandidate.Solver.Input.ScopedCallNone
import InitECandidate.Solver.Rlp.ListItems

namespace InitECandidate.Solver.Rlp.Unchecked
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def values (pointer : BitVec 64) : List (ValueHOL 64) := [.val (.word pointer)]
def rawLocals (pointer : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "p" then some (.val (.word pointer)) else none

theorem environment (table : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (pointer : BitVec 64) (known : table (ofString "rlp_item_total_unchecked")=some ([(ofString "p",.one)],body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite table (ofString "rlp_item_total_unchecked") (values pointer)=some (body,callee,.one) ∧
      callee.lookup (ofString "p")=some (.val (.word pointer)) := by
  have valid : ([(ofString "p",ShapeHOL.one)].map Prod.fst).Nodup ∧
      [(ofString "p",ShapeHOL.one)].length=(values pointer).length ∧
      (([(ofString "p",ShapeHOL.one)].zip (values pointer)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    simp [values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact table (ofString "rlp_item_total_unchecked") (values pointer)=some (body,rawLocals pointer,.one) := by
    simp only [lookupCodeHOLExact,known,valid]
    rfl
  obtain ⟨callee,called,locals⟩ := WitnessRadix.CodeEnvironment.finite_lookup table _ _ _ _ _ raw
  refine ⟨callee,called,?_⟩
  rw [locals]
  simp [rawLocals]

set_option maxRecDepth 10000 in
theorem readonly (code) (installed : Input.OriginalCode.Installed code) : Input.LocalEffects.Preserves code body := by
  simp only [body,Guest.Software.guestFn_rlp_item_total_unchecked,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  repeat first
    | apply Input.LocalEffects.sequence
    | apply Input.LocalEffects.declared
    | apply Input.LocalEffects.conditional
    | exact Input.LocalEffects.returned code _
    | exact Input.LocalEffects.skip code
    | apply Input.LocalEffects.scoped_body code _ .one (ofString "rlp_read_length") _ _ ReadLength.formals ReadLength.body .one
        (ReadLength.original_code code installed) (ReadLength.readonly code installed)

/-- Actual unchecked calls recover a previously established item's exact
total and genuine readonly continuation, paying at most ten source ticks. -/
theorem scoped_none_item (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (item : ListItem)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (values pointer))
    (encoding : Header.Encoded source pointer item.header item.payload item.flag)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "rlp_item_total_unchecked") arguments continuation)=(none,post)) :
    ∃ paid inner,1≤paid ∧ paid≤10 ∧ paid≤source.clock ∧
      evaluateHOLFiniteState (bind {source with clock:=source.clock-paid} name item.total) continuation=(none,inner) ∧
      post=restore source name inner := by
  obtain ⟨callee,called,pointerLocal⟩ := environment source.code.lookup pointer (original_code source.code installed)
  obtain ⟨positive,target,answer,inner,bodyRun,checked,continuationRun,restored⟩ :=
    Input.CallNormal.scoped_none source post name .one (ofString "rlp_item_total_unchecked") arguments _ body continuation callee .one args called normal
  obtain ⟨header,payload,flag,actualEncoding,answerEq⟩ := body_encoding (callEntryStateHOLFinite source callee) target pointer pointerLocal installed answer bodyRun
  have currentEncoding : Header.Encoded source pointer header payload flag := actualEncoding
  obtain ⟨headEq,payloadEq,flagEq⟩ := Header.Encoded.unique source pointer item.header item.payload item.flag header payload flag encoding currentEncoding
  rw [←headEq,←payloadEq] at answerEq
  rw [answerEq] at continuationRun
  have fields := readonly source.code installed (callEntryStateHOLFinite source callee) rfl
  rw [bodyRun] at fields
  change Input.LocalEffects.erase target=Input.LocalEffects.erase source at fields
  have clock := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) body
  have price := body_price source.code installed (callEntryStateHOLFinite source callee) rfl
  rw [bodyRun] at clock price
  change target.clock≤source.clock-1 at clock
  change source.clock-1-target.clock≤9 at price
  let paid := source.clock-target.clock
  have remaining : source.clock-paid=target.clock := by dsimp [paid]; omega
  have canonical : Input.CallNormal.continuationEntry source target name (.val (.word item.total))=
      bind {source with clock:=source.clock-paid} name item.total := by
    have reset := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals,clock:=target.clock}) fields
    change {target with locals:=source.locals}={source with clock:=target.clock} at reset
    unfold Input.CallNormal.continuationEntry
    rw [reset,remaining]
    rfl
  change evaluateHOLFiniteState (Input.CallNormal.continuationEntry source target name (.val (.word item.total))) continuation=(none,inner) at continuationRun
  rw [canonical] at continuationRun
  exact ⟨paid,inner,by dsimp [paid]; omega,by dsimp [paid]; omega,Nat.sub_le _ _,continuationRun,restored⟩

end InitECandidate.Solver.Rlp.Unchecked

#print axioms InitECandidate.Solver.Rlp.Unchecked.environment
#print axioms InitECandidate.Solver.Rlp.Unchecked.readonly
#print axioms InitECandidate.Solver.Rlp.Unchecked.scoped_none_item
