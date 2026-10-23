import InitECandidate.Solver.Mpt.DeleteDescentPure
import InitECandidate.Solver.Mpt.DeleteDescentLeafProgram
import InitECandidate.Solver.Input.AssignNormal

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The real comparison guard consumes the actual returned word. A
nonzero result selects res0; a zero result retains the current registered
res. Neither branch changes heap, cursors or the closed registry. -/
theorem leaf_compared_model (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (answer : BitVec 64)
    (answerCell : source.locals.lookup (ofString "eq")=some (.val (.word answer)))
    (normal : evaluateHOLFiniteState source leafCompared=(none,target)) :
    ∃ next : DescentModel target key length limit nodeLower pathLower property,
      next.pending.heap=model.pending.heap ∧ next.pending.cursor=model.pending.cursor ∧ next.pending.frame=model.pending.frame ∧
      next.pending.graph.valid=model.pending.graph.valid ∧ next.go=model.go := by
  rw [leaf_shapes.2.2.2,evaluateHOLFiniteState_ite] at normal
  by_cases zero : answer=0#64
  · have actual : evaluateHOLFiniteState source .skip=(none,target):=by
      simpa [evalHOLExact,toExact,localVar,answerCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL] using normal
    have endpoint : target=source:=congrArg Prod.snd (actual.symm.trans (evaluateHOLFiniteState_skip source))
    subst target
    exact ⟨model,rfl,rfl,rfl,rfl,rfl⟩
  · have actual : evaluateHOLFiniteState source (.assign .local (ofString "res") (.const 0#64))=(none,target):=by
      simpa [evalHOLExact,toExact,localVar,answerCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL] using normal
    have endpoint:=Input.assign_none source target "res" (.const 0#64) 0#64 rfl actual
    rw [endpoint]
    exact ⟨model.bind_result source key length limit nodeLower pathLower property 0#64 model.pending.graph.null,rfl,rfl,rfl,rfl,rfl⟩

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.leaf_compared_model
