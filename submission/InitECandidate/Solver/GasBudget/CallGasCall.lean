import InitECandidate.Solver.GasBudget.CallGas

namespace InitECandidate.Solver.GasBudget.CallGas
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def values (words : U256Zero.Quad) (requested left : BitVec 64) : List (ValueHOL 64) :=
  [Input.RlpWrite.U256Value.tuple words,.val (.word requested),.val (.word left),.val (.word 0#64),.val (.word 0#64)]
def rawLocals (words : U256Zero.Quad) (requested left : BitVec 64) (name : MlS) : Option (ValueHOL 64) :=
  if name=ofString "extra_gas" then some (.val (.word 0#64)) else if name=ofString "memory_cost" then some (.val (.word 0#64))
  else if name=ofString "gas_left" then some (.val (.word left)) else if name=ofString "gas" then some (.val (.word requested))
  else if name=ofString "value" then some (Input.RlpWrite.U256Value.tuple words) else none

theorem environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (words : U256Zero.Quad) (requested left : BitVec 64)
    (lookup : codeFn (ofString "calculate_message_call_gas")=some (formals,body,returnShape)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "calculate_message_call_gas") (values words requested left)=some (body,callee,returnShape) ∧
      (∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,source.locals=callee→Inputs source words requested left) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values words requested left).length ∧
      ((formals.zip (values words requested left)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,Input.RlpWrite.U256Value.tupleShape,Input.RlpWrite.U256Value.tuple,shapeOfHOLExact,shapeEqHOL_eq_true]
  have raw : lookupCodeHOLExact codeFn (ofString "calculate_message_call_gas") (values words requested left)=some (body,rawLocals words requested left,returnShape) := by
    simp only [lookupCodeHOLExact,lookup,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩:=WitnessRadix.CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_⟩
  intro source sourceLocals
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals rw [sourceLocals,locals]
  · simp [rawLocals,show ofString "value"≠ofString "extra_gas" from by decide,show ofString "value"≠ofString "memory_cost" from by decide,
      show ofString "value"≠ofString "gas_left" from by decide,show ofString "value"≠ofString "gas" from by decide]
  · simp [rawLocals,show ofString "gas"≠ofString "extra_gas" from by decide,show ofString "gas"≠ofString "memory_cost" from by decide,show ofString "gas"≠ofString "gas_left" from by decide]
  · simp [rawLocals,show ofString "gas_left"≠ofString "extra_gas" from by decide,show ofString "gas_left"≠ofString "memory_cost" from by decide]
  · simp [rawLocals,show ofString "memory_cost"≠ofString "extra_gas" from by decide]
  · simp [rawLocals]

def callerPost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (debit forwarded : BitVec 64) :=
  setVarHOLFinite (ofString name) (pair debit forwarded) {source with clock:=source.clock-3}

/-- Real five-argument, two-word-return call in the mode used by CALL,
CALLCODE, DELEGATECALL and STATICCALL, including the outer call clock. -/
theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : U256Zero.Quad) (requested left : BitVec 64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (values words requested left))
    (code : source.code.lookup (ofString "calculate_message_call_gas")=some (formals,body,returnShape))
    (zeroCode : source.code.lookup (ofString "u256_is_zero")=some (U256Zero.formals,U256Zero.body,.one))
    (addCode : source.code.lookup (ofString "add_sat")=some (AddExact.formals,AddExact.body,.one)) (enough : 3≤source.clock) :
    evaluateHOLFiniteState source (.decCall (ofString name) returnShape (ofString "calculate_message_call_gas") expressions continuation)=
      (let output:=evaluateHOLFiniteState (callerPost source name (capped requested left) (capped requested left+stipend words)) continuation
      (output.1,restore source name output.2)) := by
  obtain ⟨callee,called,inputs⟩:=environment source.code.lookup words requested left code
  let entry:=callEntryStateHOLFinite source callee
  have entryInputs : Inputs entry words requested left:=inputs entry rfl
  obtain ⟨target,run,frame⟩:=execute entry words requested left entryInputs zeroCode addCode (by change 2≤source.clock-1; omega)
  have actual:=Input.CallNormal.return_execute source target name returnShape (ofString "calculate_message_call_gas") expressions (values words requested left)
    body continuation callee returnShape (pair (capped requested left) (capped requested left+stipend words)) args called (by omega) run
      (by simp [pair,returnShape,shapeOfHOLExact,shapeEqHOL_eq_true])
  have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) frame
  change {target with locals:=source.locals}={source with clock:=source.clock-1-2} at callerFrame
  have sub : source.clock-1-2=source.clock-3 := by omega
  rw [sub] at callerFrame
  have canonical : Input.CallNormal.continuationEntry source target name (pair (capped requested left) (capped requested left+stipend words))=
      callerPost source name (capped requested left) (capped requested left+stipend words) := by
    exact congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>setVarHOLFinite (ofString name) (pair (capped requested left) (capped requested left+stipend words)) state) callerFrame
  rw [canonical] at actual
  exact actual

end InitECandidate.Solver.GasBudget.CallGas

#print axioms InitECandidate.Solver.GasBudget.CallGas.environment
#print axioms InitECandidate.Solver.GasBudget.CallGas.call_execute
