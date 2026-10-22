import InitECandidate.Solver.Input.CallPrefixDeclaration
import InitECandidate.Solver.Input.RlpWrite.U256Shape

namespace InitECandidate.Solver.Input.CallPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem Execution.declare_checked {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {name : MlS} {shape : ShapeHOL} {expression : ExpHOL 64} {rest : List Action}
    (execution : Execution source (.declare name shape expression::rest) target) :
    ∃ value,WitnessRadix.QueryBranch.eval source expression=some value ∧
      shapeOfHOLExact value=shape ∧ Execution (setVarHOLFinite name value source) rest target := by
  cases execution with
  | step first next=>
    cases first with
    | declare _ _ _ value read checked=>
      exact ⟨value,read,((shapeEqHOL_eq_true _ _).mp checked).symm,next⟩

/-- The genuine checked declaration supplies its actual four word leaves;
the caller need not predict the result of the byte-expression evaluation. -/
theorem Execution.declare_words {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {name : MlS} {expression : ExpHOL 64} {rest : List Action}
    (execution : Execution source (.declare name RlpWrite.U256Value.tupleShape expression::rest) target) :
    ∃ words : RlpWrite.U256Value.Words,WitnessRadix.QueryBranch.eval source expression=some (RlpWrite.U256Value.tuple words) ∧
      Execution (setVarHOLFinite name (RlpWrite.U256Value.tuple words) source) rest target := by
  obtain ⟨value,read,shape,next⟩:=execution.declare_checked
  obtain ⟨words,same⟩:=RlpWrite.U256Value.of_shape value shape
  subst value
  exact ⟨words,read,next⟩

end InitECandidate.Solver.Input.CallPrefix

#print axioms InitECandidate.Solver.Input.CallPrefix.Execution.declare_checked
#print axioms InitECandidate.Solver.Input.CallPrefix.Execution.declare_words
