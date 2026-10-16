import InitECandidate.Solver.FlattenWeighted.LoopTimeout

namespace InitECandidate.Solver.FlattenWeighted
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate

/-- Two non-timeout runs with different initial clocks agree on their result
and every final state field other than unused clock. Both runs are compared at
the common clock source.clock+clock using the original clock-extension theorem. -/
theorem reclockAgreement {width : Nat} [NeZero width] {C F : Type}
    (prog : HolProg width) (source : StackSemStateFiniteExact width C F) (clock : Nat)
    (result boundedResult : Option (StackSemResult width))
    (post boundedPost : StackSemStateFiniteExact width C F)
    (execution : evaluate (prog, source) = (result, post))
    (boundedExecution : evaluate (prog, {source with clock := clock}) = (boundedResult, boundedPost))
    (notTimeout : result ≠ some .timeOut) (boundedNotTimeout : boundedResult ≠ some .timeOut) :
    result = boundedResult ∧ {post with clock := 0} = {boundedPost with clock := 0} := by
  have left := StackProps.evaluateAddClock clock prog source result post ⟨execution, notTimeout⟩
  have right := StackProps.evaluateAddClock source.clock prog {source with clock := clock}
    boundedResult boundedPost ⟨boundedExecution, boundedNotTimeout⟩
  simp only [Nat.add_comm clock source.clock] at right
  have same := left.symm.trans right
  constructor
  · exact congrArg Prod.fst same
  · exact congrArg (fun pair => {pair.2 with clock := 0}) same

end InitECandidate.Solver.FlattenWeighted
#print axioms InitECandidate.Solver.FlattenWeighted.reclockAgreement
