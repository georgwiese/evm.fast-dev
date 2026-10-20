import InitECandidate.Solver.Input.FqNegExecution

namespace InitECandidate.Solver.Input.FqNeg
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
set_option maxRecDepth 100000

theorem environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (a : Words)
    (code : codeFn (ofString "fq_neg") = some (formals,body,RlpWrite.U256Value.tupleShape)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "fq_neg") [RlpWrite.U256Value.tuple a] = some (body,callee,RlpWrite.U256Value.tupleShape) ∧
      callee.lookup (ofString "a") = some (RlpWrite.U256Value.tuple a) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length = ([RlpWrite.U256Value.tuple a] : List (ValueHOL 64)).length ∧
      ((formals.zip [RlpWrite.U256Value.tuple a]).all (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
    simp [formals,RlpWrite.U256Value.tupleShape,RlpWrite.U256Value.tuple,shapeOfHOLExact,shapeEqHOL_eq_true]
  have raw : lookupCodeHOLExact codeFn (ofString "fq_neg") [RlpWrite.U256Value.tuple a] = some (body,RlpWrite.U256Value.rawLocals a,RlpWrite.U256Value.tupleShape) := by
    simp only [lookupCodeHOLExact,code,valid,↓reduceIte]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  refine ⟨callee,called,?_⟩
  rw [locals]
  simp [RlpWrite.U256Value.rawLocals]

/-- Real scoped fq_neg returns its actual quad in at most three ticks and
preserves every nonlocal field, including all accumulated FFI events. -/
theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a : Words)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) arguments = some [RlpWrite.U256Value.tuple a])
    (enough : 3 ≤ source.clock) :
    ∃ answer paid,paid ≤ 3 ∧
      evaluateHOLFiniteState source (.decCall (ofString name) RlpWrite.U256Value.tupleShape (ofString "fq_neg") arguments continuation) =
        (let output := evaluateHOLFiniteState (setVarHOLFinite (ofString name) (RlpWrite.U256Value.tuple answer) {source with clock := source.clock - paid}) continuation;
          (output.1,restore source name output.2)) := by
  obtain ⟨callee,called,aRead⟩ := environment source.code.lookup a (original_code source.code installed)
  let inner := callEntryStateHOLFinite source callee
  obtain ⟨target,answer,paid,run,bound,frame⟩ := execute inner a aRead installed (by change 2 ≤ source.clock - 1; omega)
  have actual := CallNormal.return_execute source target name RlpWrite.U256Value.tupleShape (ofString "fq_neg") arguments [RlpWrite.U256Value.tuple a] body continuation callee
    RlpWrite.U256Value.tupleShape (RlpWrite.U256Value.tuple answer) args called (by omega) run
    (by simp [RlpWrite.U256Value.tuple,RlpWrite.U256Value.tupleShape,shapeOfHOLExact,shapeEqHOL_eq_true])
  have caller := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals}) frame
  have clock : source.clock - 1 - paid = source.clock - (paid + 1) := by omega
  have same : CallNormal.continuationEntry source target name (RlpWrite.U256Value.tuple answer) =
      setVarHOLFinite (ofString name) (RlpWrite.U256Value.tuple answer) {source with clock := source.clock - (paid + 1)} := by
    change setVarHOLFinite (ofString name) (RlpWrite.U256Value.tuple answer) {target with locals := source.locals} = _
    have fields : {target with locals := source.locals} = {source with clock := source.clock - (paid + 1)} := by
      change {target with locals := source.locals} = {source with clock := source.clock - 1 - paid} at caller
      rw [clock] at caller
      exact caller
    rw [fields]
  rw [same] at actual
  exact ⟨answer,paid + 1,by omega,actual⟩

end InitECandidate.Solver.Input.FqNeg

#print axioms InitECandidate.Solver.Input.FqNeg.call_execute

#print axioms InitECandidate.Solver.Input.FqNeg.environment
