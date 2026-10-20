import InitECandidate.Solver.GasBudget.U256Arithmetic
import InitECandidate.Solver.Input.PureValueReturn

namespace InitECandidate.Solver.GasBudget.U256Add
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem success_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : Quad)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) arguments =
      some [Input.RlpWrite.U256Value.tuple a,Input.RlpWrite.U256Value.tuple b])
    (code : source.code.lookup (ofString "u256_add") = some (formals,body,Input.RlpWrite.U256Value.tupleShape))
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) Input.RlpWrite.U256Value.tupleShape (ofString "u256_add") arguments continuation) = (some (.returned returned),post)) :
    1 ≤ source.clock ∧ ∃ inner,
      evaluateHOLFiniteState (setVarHOLFinite (ofString name) (Input.RlpWrite.U256Value.tuple (result a b)) {source with clock := source.clock - 1}) continuation = (some (.returned returned),inner) ∧
      post = restore source name inner := by
  obtain ⟨callee,called,aLocal,bLocal⟩ := environment source.code.lookup a b code
  obtain ⟨positive,target,answer,inner,bodyRun,typed,tailRun,restored⟩ := Input.CallNormal.scoped_normal source post name Input.RlpWrite.U256Value.tupleShape
    (ofString "u256_add") arguments _ body continuation callee Input.RlpWrite.U256Value.tupleShape args called returned normal
  let entry := callEntryStateHOLFinite source callee
  have actual := Input.CallNormal.pure_value_execute source name Input.RlpWrite.U256Value.tupleShape (ofString "u256_add") arguments _ body continuation callee
    Input.RlpWrite.U256Value.tupleShape (Input.RlpWrite.U256Value.tuple (result a b)) args called positive (execute entry a b aLocal bLocal)
    (by simp [Input.RlpWrite.U256Value.tuple,Input.RlpWrite.U256Value.tupleShape,shapeOfHOLExact,shapeEqHOL_eq_true])
  have same := normal.symm.trans actual
  have first := congrArg Prod.fst same
  have last := congrArg Prod.snd same
  refine ⟨positive,(evaluateHOLFiniteState (setVarHOLFinite (ofString name) (Input.RlpWrite.U256Value.tuple (result a b)) {source with clock := source.clock - 1}) continuation).2,?_,last⟩
  apply Prod.ext
  · exact first.symm
  · rfl

end InitECandidate.Solver.GasBudget.U256Add

#print axioms InitECandidate.Solver.GasBudget.U256Add.success_prefix

namespace InitECandidate.Solver.GasBudget.U256Sub
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem success_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : Quad)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) arguments =
      some [Input.RlpWrite.U256Value.tuple a,Input.RlpWrite.U256Value.tuple b])
    (code : source.code.lookup (ofString "u256_sub") = some (formals,body,Input.RlpWrite.U256Value.tupleShape))
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) Input.RlpWrite.U256Value.tupleShape (ofString "u256_sub") arguments continuation) = (some (.returned returned),post)) :
    1 ≤ source.clock ∧ ∃ inner,
      evaluateHOLFiniteState (setVarHOLFinite (ofString name) (Input.RlpWrite.U256Value.tuple (result a b)) {source with clock := source.clock - 1}) continuation = (some (.returned returned),inner) ∧
      post = restore source name inner := by
  obtain ⟨callee,called,aLocal,bLocal⟩ := environment source.code.lookup a b code
  obtain ⟨positive,target,answer,inner,bodyRun,typed,tailRun,restored⟩ := Input.CallNormal.scoped_normal source post name Input.RlpWrite.U256Value.tupleShape
    (ofString "u256_sub") arguments _ body continuation callee Input.RlpWrite.U256Value.tupleShape args called returned normal
  let entry := callEntryStateHOLFinite source callee
  have actual := Input.CallNormal.pure_value_execute source name Input.RlpWrite.U256Value.tupleShape (ofString "u256_sub") arguments _ body continuation callee
    Input.RlpWrite.U256Value.tupleShape (Input.RlpWrite.U256Value.tuple (result a b)) args called positive (execute entry a b aLocal bLocal)
    (by simp [Input.RlpWrite.U256Value.tuple,Input.RlpWrite.U256Value.tupleShape,shapeOfHOLExact,shapeEqHOL_eq_true])
  have same := normal.symm.trans actual
  have first := congrArg Prod.fst same
  have last := congrArg Prod.snd same
  refine ⟨positive,(evaluateHOLFiniteState (setVarHOLFinite (ofString name) (Input.RlpWrite.U256Value.tuple (result a b)) {source with clock := source.clock - 1}) continuation).2,?_,last⟩
  apply Prod.ext
  · exact first.symm
  · rfl

end InitECandidate.Solver.GasBudget.U256Sub

#print axioms InitECandidate.Solver.GasBudget.U256Sub.success_prefix
