import InitECandidate.Solver.GasBudget.FrameExceptionProgram
import InitECandidate.Solver.Input.LoopNormal

namespace InitECandidate.Solver.GasBudget.FrameException
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

def choicePrice (err : BitVec 64) : Nat := if err = 1#64 then 0 else 1

theorem clear_data_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame empty : BitVec 64)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (emptyGlobal : source.globals.lookup (ofString "evm_empty") = some (.val (.word empty)))
    (normal : evaluateHOLFiniteState source clearData = (none, target)) :
    target = {source with memory := target.memory} ∧ regularBudget target.memory frame = regularBudget source.memory frame := by
  obtain ⟨first, firstRun, lastRun⟩ := Input.sequence_none source target _ _ normal
  have emptyRead : eval source (.var .global (ofString "evm_empty")) = some (.val (.word empty)) := by
    simpa only [eval, evalHOLExact, toExact] using emptyGlobal
  have firstEq := FrameField.normal_word source first frame 120#64 empty _ ev emptyRead firstRun
  have firstEV : first.globals.lookup (ofString "ev") = some (.val (.word frame)) := by rw [firstEq]; exact ev
  have lastEq := FrameField.normal_word first target frame 128#64 0#64 (.const 0#64) firstEV rfl lastRun
  have targetEq : target = {source with memory := StoreWord.put (StoreWord.put source.memory (frame + 120#64) empty) (frame + 128#64) 0#64} := by
    rw [lastEq, firstEq]
  refine ⟨by rw [targetEq], ?_⟩
  rw [targetEq]
  exact (FrameField.put_budget _ frame 128#64 0#64 (by decide) (by decide) (by decide)).trans
    (FrameField.put_budget source.memory frame 120#64 empty (by decide) (by decide) (by decide))

/-- Both actual exception branches retain the regular ledger. EvmErr1 marks
the error directly; every other error executes the real halt and clears the
return-data fields. Only the latter branch pays a halt call clock. -/
theorem choice_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame err empty : BitVec 64)
    (errLocal : source.locals.lookup (ofString "err") = some (.val (.word err)))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (emptyGlobal : source.globals.lookup (ofString "evm_empty") = some (.val (.word empty)))
    (haltCode : source.code.lookup (ofString "frame_halt") = some (Halt.formals, Halt.body, .one))
    (mapped : ∀ offset ∈ ([64, 160, 184] : List Nat), source.memaddrs (frame + BitVec.ofNat 64 offset))
    (cap : regularBudget source.memory frame ≤ 16777216)
    (normal : evaluateHOLFiniteState source choice = (none, target)) :
    choicePrice err ≤ source.clock ∧ target = {source with memory := target.memory, clock := source.clock - choicePrice err} ∧
      regularBudget target.memory frame = regularBudget source.memory frame := by
  have test : eval source condition = some (.val (.word (if err = 1#64 then 0#64 else 1#64))) := by
    simp [eval, condition, evalHOLExact, toExact, localVar, errLocal, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  simp only [eval] at test
  rw [choice, evaluateHOLFiniteState_ite, test] at normal
  by_cases same : err = 1#64
  · have specialRun : evaluateHOLFiniteState source specialError = (none, target) := by simpa [same] using normal
    have errRead : eval source (localVar "err") = some (.val (.word err)) := by simpa only [eval, localVar, evalHOLExact, toExact] using errLocal
    have targetEq := FrameField.normal_word source target frame 160#64 err (localVar "err") ev errRead specialRun
    refine ⟨by simp [choicePrice, same], ?_, ?_⟩
    · rw [targetEq]; simp [choicePrice, same]
    · rw [targetEq]
      exact FrameField.put_budget source.memory frame 160#64 err (by decide) (by decide) (by decide)
  · have regularRun : evaluateHOLFiniteState source regularError = (none, target) := by simpa [same] using normal
    obtain ⟨called, haltRun, clearRun⟩ := Input.sequence_none source target halt clearData regularRun
    have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [localVar "err"] = some [.val (.word err)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, localVar, toExact, errLocal]
    cases gasCell : source.memory (frame + 64#64) with
    | word gas =>
      cases usedCell : source.memory (frame + 184#64) with
      | word used =>
        obtain ⟨positive, clock, halted, haltBudget, _, _⟩ := Halt.call_normal source called frame gas used err _ args haltCode ev mapped gasCell usedCell cap haltRun
        have calledEV : called.globals.lookup (ofString "ev") = some (.val (.word frame)) := by rw [halted]; exact ev
        have calledEmpty : called.globals.lookup (ofString "evm_empty") = some (.val (.word empty)) := by rw [halted]; exact emptyGlobal
        obtain ⟨cleared, clearBudget⟩ := clear_data_normal called target frame empty calledEV calledEmpty clearRun
        have frameEq := cleared.trans (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with memory := target.memory}) halted)
        refine ⟨by simpa [choicePrice, same] using positive, ?_, clearBudget.trans haltBudget⟩
        simpa only [choicePrice, if_neg same] using frameEq

end InitECandidate.Solver.GasBudget.FrameException

#print axioms InitECandidate.Solver.GasBudget.FrameException.clear_data_normal
#print axioms InitECandidate.Solver.GasBudget.FrameException.choice_normal
