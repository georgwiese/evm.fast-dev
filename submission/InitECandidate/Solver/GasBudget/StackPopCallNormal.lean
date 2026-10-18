import InitECandidate.Solver.GasBudget.StackPopNormal
import InitECandidate.Solver.Input.ScopedCallNormal

namespace InitECandidate.Solver.GasBudget.StackPop
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

def shape : ShapeHOL := .comb [.one, .one, .one, .one]
def resumed (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame sp : BitVec 64) (name : String) (value : ValueHOL 64) :=
  setVarHOLFinite (ofString name) value
    {source with memory := StoreWord.put source.memory (frame + 16#64) (sp - 1#64), clock := source.clock - 1}

/-- Actual tuple-valued stack_pop declaration inside an opcode: its genuine
returned value enters the real continuation after precisely the sp write and
one caller clock. No callee/continuation execution is supplied as a premise. -/
theorem call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (name : String) (continuation : ProgHOL 64)
    (code : source.code.lookup (ofString "stack_pop") = some ([], body, shape))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) shape (ofString "stack_pop") [] continuation) = (some (.returned value), post)) :
    1 ≤ source.clock ∧ ∃ sp returned inner,
      source.memaddrs (frame + 16#64) ∧ source.memory (frame + 16#64) = .word sp ∧ sp ≠ 0#64 ∧
      shapeEqHOL (shapeOfHOLExact returned) shape = true ∧
      evaluateHOLFiniteState (resumed source frame sp name returned) continuation = (some (.returned value), inner) ∧
      post = restore source name inner ∧
      regularBudget (resumed source frame sp name returned).memory frame = regularBudget source.memory frame ∧
      (resumed source frame sp name returned).memory (frame + 184#64) = source.memory (frame + 184#64) := by
  have raw : lookupCodeHOLExact source.code.lookup (ofString "stack_pop") [] = some (body, (fun _ => none), shape) := by
    simp [lookupCodeHOLExact, code]
  obtain ⟨callee, called, locals⟩ := CodeEnvironment.finite_lookup source.code.lookup (ofString "stack_pop") [] body (fun _ => none) shape raw
  obtain ⟨positive, target, returned, inner, bodyRun, valid, continuationRun, postEq⟩ :=
    Input.CallNormal.scoped_normal source post name shape (ofString "stack_pop") [] [] body continuation callee shape rfl called value normal
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨sp, mapped, spCell, nonzero, clock, frameEq, budget, usedSame, away⟩ := body_normal entry target frame ev returned bodyRun
  have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals}) frameEq
  have nextEq : Input.CallNormal.continuationEntry source target name returned = resumed source frame sp name returned := by
    exact congrArg (setVarHOLFinite (ofString name) returned) callerFrame
  rw [nextEq] at continuationRun
  refine ⟨positive, sp, returned, inner, mapped, spCell, nonzero, (Bool.and_eq_true_iff.mp valid).1, continuationRun, postEq, ?_, ?_⟩
  · exact FrameField.put_budget source.memory frame 16#64 (sp - 1#64) (by decide) (by decide) (by decide)
  · exact FrameField.put_other source.memory frame 16#64 (sp - 1#64) 184#64 (by decide)

end InitECandidate.Solver.GasBudget.StackPop

#print axioms InitECandidate.Solver.GasBudget.StackPop.call_normal
