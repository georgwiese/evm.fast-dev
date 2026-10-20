import InitECandidate.Solver.GasBudget.U256LessThan
import InitECandidate.Solver.Input.PureValueReturn

namespace InitECandidate.Solver.GasBudget.U256LessThan
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem success_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : Quad)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) arguments =
      some [Input.RlpWrite.U256Value.tuple a,Input.RlpWrite.U256Value.tuple b])
    (code : source.code.lookup (ofString "u256_lt") = some (formals,body,.one))
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "u256_lt") arguments continuation) = (some (.returned returned),post)) :
    1 ≤ source.clock ∧ ∃ inner,
      evaluateHOLFiniteState (setVarHOLFinite (ofString name) (.val (.word (resultWord a b))) {source with clock := source.clock - 1}) continuation = (some (.returned returned),inner) ∧
      post = restore source name inner := by
  obtain ⟨callee,called,aLocal,bLocal⟩ := environment source.code.lookup a b code
  obtain ⟨positive,target,answer,inner,bodyRun,typed,tailRun,restored⟩ := Input.CallNormal.scoped_normal source post name .one
    (ofString "u256_lt") arguments _ body continuation callee .one args called returned normal
  let entry := callEntryStateHOLFinite source callee
  have actual := Input.CallNormal.pure_value_execute source name .one (ofString "u256_lt") arguments _ body continuation callee
    .one (.val (.word (resultWord a b))) args called positive ⟨emptyLocalsHOLFinite entry,execute entry a b aLocal bLocal,rfl⟩
    (by simp [shapeOfHOLExact,shapeEqHOL_eq_true])
  have same := normal.symm.trans actual
  have first := congrArg Prod.fst same
  have last := congrArg Prod.snd same
  refine ⟨positive,(evaluateHOLFiniteState (setVarHOLFinite (ofString name) (.val (.word (resultWord a b))) {source with clock := source.clock - 1}) continuation).2,?_,last⟩
  apply Prod.ext
  · exact first.symm
  · rfl

end InitECandidate.Solver.GasBudget.U256LessThan

#print axioms InitECandidate.Solver.GasBudget.U256LessThan.success_prefix

