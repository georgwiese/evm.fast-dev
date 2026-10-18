import InitECandidate.Solver.GasBudget.StackPopOutcomes
import InitECandidate.Solver.GasBudget.StackPopCallNormal
import InitECandidate.Solver.Input.ScopedCallException
import InitECandidate.Solver.Input.LocalEffectsCall

namespace InitECandidate.Solver.GasBudget.StackPop
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

/-- An actual pop-declaration exception either is genuine empty-stack
underflow before mutation, or comes from its real continuation after one
successful pop. No future callee run, funding or tuple read is assumed. -/
theorem call_exception (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame sp : BitVec 64)
    (name : String) (continuation : ProgHOL 64)
    (code : source.code.lookup (ofString "stack_pop") = some ([], body, shape))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (mapped : source.memaddrs (frame + 16#64)) (cell : source.memory (frame + 16#64) = .word sp)
    (exceptionShape : source.eshapes.lookup (ofString "EvmErr") = some .one)
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) shape (ofString "stack_pop") [] continuation) =
      (some (.exception identifier payload), post)) :
    1 ≤ source.clock ∧
      ((sp = 0#64 ∧ identifier = ofString "EvmErr" ∧ payload = .val (.word 2#64) ∧
          emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with clock := source.clock - 1} ∧
          post.clock = source.clock - 1) ∨
       (sp ≠ 0#64 ∧ ∃ returned inner,
          shapeEqHOL (shapeOfHOLExact returned) shape = true ∧
          evaluateHOLFiniteState (resumed source frame sp name returned) continuation = (some (.exception identifier payload), inner) ∧
          post = restore source name inner ∧
          regularBudget (resumed source frame sp name returned).memory frame = regularBudget source.memory frame ∧
          (resumed source frame sp name returned).memory (frame + 184#64) = source.memory (frame + 184#64))) := by
  obtain ⟨positive, values, actualBody, callee, returnShape, target, args, called, cases⟩ :=
    Input.CallNormal.scoped_exception_data source post name shape (ofString "stack_pop") [] continuation identifier payload run
  have identified := Input.LocalEffects.lookup_body source.code (ofString "stack_pop") [] body shape code values actualBody callee returnShape called
  rw [identified] at cases
  let entry := callEntryStateHOLFinite source callee
  rcases cases with failed | returned
  · obtain ⟨bodyRun, postEq⟩ := failed
    obtain ⟨zero, actualId, actualPayload, frameEq, clock⟩ :=
      exception_underflow entry target frame sp ev mapped cell exceptionShape identifier payload bodyRun
    refine ⟨positive, Or.inl ⟨zero, actualId, actualPayload, ?_, ?_⟩⟩
    · rw [postEq]
      exact frameEq
    · rw [postEq]
      exact clock
  · obtain ⟨returned, inner, bodyRun, checked, continuationRun, postEq⟩ := returned
    obtain ⟨actualSP, actualMapped, actualCell, nonzero, clock, frameEq, budget, usedSame, outside⟩ :=
      body_normal entry target frame ev returned bodyRun
    have sameSP : actualSP = sp := HolWordLab.word.inj (actualCell.symm.trans cell)
    rw [sameSP] at nonzero frameEq
    have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals}) frameEq
    have nextEq : Input.CallNormal.continuationEntry source target name returned = resumed source frame sp name returned :=
      congrArg (setVarHOLFinite (ofString name) returned) callerFrame
    rw [nextEq] at continuationRun
    refine ⟨positive, Or.inr ⟨nonzero, returned, inner, (Bool.and_eq_true_iff.mp checked).1, continuationRun, postEq, ?_, ?_⟩⟩
    · exact FrameField.put_budget source.memory frame 16#64 (sp - 1#64) (by decide) (by decide) (by decide)
    · exact FrameField.put_other source.memory frame 16#64 (sp - 1#64) 184#64 (by decide)

end InitECandidate.Solver.GasBudget.StackPop

#print axioms InitECandidate.Solver.GasBudget.StackPop.call_exception
