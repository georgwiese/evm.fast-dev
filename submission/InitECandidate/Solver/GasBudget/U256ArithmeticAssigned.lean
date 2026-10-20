import InitECandidate.Solver.GasBudget.U256Arithmetic
import InitECandidate.Solver.Input.AssignedCallNormal

namespace InitECandidate.Solver.GasBudget.U256Add
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The actual assignment used by move_ether retains every nonlocal field
and replaces its existing four-word local in exactly one source tick. -/
theorem assigned (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (a b old : Quad)
    (name : String) (arguments : List (ExpHOL 64))
    (binding : source.locals.lookup (ofString name) = some (Input.RlpWrite.U256Value.tuple old))
    (args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) arguments =
      some [Input.RlpWrite.U256Value.tuple a,Input.RlpWrite.U256Value.tuple b])
    (code : source.code.lookup (ofString "u256_add") = some (formals,body,Input.RlpWrite.U256Value.tupleShape))
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,ofString name),none)) (ofString "u256_add") arguments) = (none,post)) :
    1 ≤ source.clock ∧ post = setVarHOLFinite (ofString name) (Input.RlpWrite.U256Value.tuple (result a b)) {source with clock := source.clock - 1} := by
  obtain ⟨callee,called,aLocal,bLocal⟩ := environment source.code.lookup a b code
  obtain ⟨positive,normalTarget,normalAnswer,bodyRun⟩ := Input.CallNormal.assigned_callee_return source post (some (.local,ofString name)) (ofString "u256_add") arguments _ body callee Input.RlpWrite.U256Value.tupleShape args called normal
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨target,run,frame⟩ := execute entry a b aLocal bLocal
  have valid : isValidValueHOLExact source.toExact .local (ofString name) (Input.RlpWrite.U256Value.tuple (result a b)) = true := by
    simp [isValidValueHOLExact,lookupKvarHOLExact,binding,Input.RlpWrite.U256Value.tuple,shapeOfHOLExact,shapeEqHOL_eq_true]
  have actual := evaluateHOLFiniteState_call_return_set_kvar source .local (ofString name) none (ofString "u256_add") arguments _ body callee Input.RlpWrite.U256Value.tupleShape
    (Input.RlpWrite.U256Value.tuple (result a b)) target args called (by omega) run
    (by simp [Input.RlpWrite.U256Value.tuple,Input.RlpWrite.U256Value.tupleShape,shapeOfHOLExact,shapeEqHOL_eq_true]) valid
  have postEq := congrArg Prod.snd (normal.symm.trans actual)
  change post = setVarHOLFinite (ofString name) (Input.RlpWrite.U256Value.tuple (result a b)) {target with locals := source.locals} at postEq
  have callerFrame : {target with locals := source.locals} = {source with clock := source.clock - 1} :=
    congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals}) frame
  exact ⟨positive,postEq.trans (congrArg (setVarHOLFinite (ofString name) (Input.RlpWrite.U256Value.tuple (result a b))) callerFrame)⟩

end InitECandidate.Solver.GasBudget.U256Add

#print axioms InitECandidate.Solver.GasBudget.U256Add.assigned
