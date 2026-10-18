import InitE.SourceSemantics
import InitECandidate.Solver.Input.OriginalExceptions
import InitECandidate.Solver.Input.DeclarationFrame

namespace InitECandidate.Solver.Input.SourceEntry
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 100000

/-- A terminating observation comes from a genuine finite source execution.
The clock is extracted, not bounded by this theorem. -/
theorem terminating_execution (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : MlS) (outcome : HolOutcome) (events : List HolIoEvent)
    (terminates : semantics source name = .terminate outcome events) :
    ∃ clock target result actualOutcome,
      evaluateHOLFiniteState {source with clock := clock} (.call none name []) = (result, target) ∧
      (match result with
       | some (.finalFfi event) => actualOutcome = HolOutcome.ffiOutcome event
       | some (.returned _) => actualOutcome = HolOutcome.success
       | _ => False) ∧
      HolBehaviour.terminate outcome events = .terminate actualOutcome target.ffi.ioEvents := by
  classical
  unfold semantics at terminates
  dsimp only at terminates
  split at terminates
  · cases terminates
  · split at terminates
    · rename_i selected chosen
      obtain ⟨clock, target, result, actualOutcome, run, classified, same⟩ := holOptionSome_some chosen
      refine ⟨clock, target, result, actualOutcome, run, ?_, terminates.symm.trans same⟩
      cases result with
      | none => exact classified
      | some result => cases result <;> exact classified
    · cases terminates

/-- The authoritative terminating source behavior exposes its real declaration
pass and main call. All original code and exception shapes follow from those
passes, including at the final state. No initialization trace is supplied. -/
theorem original_main (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (terminates : InitE.sourceBehaviour input = .terminate outcome events) :
    ∃ structs entered clock target result actualOutcome,
      decsStcnamesHOLExact [] OriginalCode.program = some structs ∧
      @evaluateDeclsHOLFinite 64 Guest.HostMemory _ {InitE.sourceInitialState input with structs := structs}
        (fun address => Classical.propDecidable (InitE.ordinaryDomain address)) OriginalCode.program = some entered ∧
      OriginalCode.Installed entered.code ∧ OriginalExceptions.Installed entered.eshapes ∧
      DeclarationCode.frame entered = DeclarationCode.frame {InitE.sourceInitialState input with structs := structs} ∧
      evaluateHOLFiniteState {entered with clock := clock} (.call none (ofString "main") []) = (result, target) ∧
      (match result with
       | some (.finalFfi event) => actualOutcome = HolOutcome.ffiOutcome event
       | some (.returned _) => actualOutcome = HolOutcome.success
       | _ => False) ∧
      HolBehaviour.terminate outcome events = .terminate actualOutcome target.ffi.ioEvents ∧
      OriginalCode.Installed target.code ∧ OriginalExceptions.Installed target.eshapes := by
  classical
  change semanticsDecls (InitE.sourceInitialState input) (ofString "main") OriginalCode.program = _ at terminates
  unfold semanticsDecls at terminates
  cases contexts : decsStcnamesHOLExact [] OriginalCode.program with
  | none => simp only [contexts] at terminates; cases terminates
  | some structs =>
      simp only [contexts] at terminates
      cases declarations : evaluateDeclsHOLFinite {InitE.sourceInitialState input with structs := structs} OriginalCode.program with
      | none => simp only [declarations] at terminates; cases terminates
      | some entered =>
          simp only [declarations] at terminates
          have code := OriginalCode.declaration_pass _ entered declarations
          have shapes := OriginalExceptions.declaration_pass _ entered declarations
          have fields := DeclarationCode.declaration_frame _ OriginalCode.program entered declarations
          obtain ⟨clock, target, result, actualOutcome, run, classified, same⟩ := terminating_execution entered _ outcome events terminates
          exact ⟨structs, entered, clock, target, result, actualOutcome, rfl, declarations, code, shapes, fields,
            run, classified, same, OriginalCode.after_execution _ _ _ _ run code,
            OriginalExceptions.after_execution _ _ _ _ run shapes⟩

end InitECandidate.Solver.Input.SourceEntry

#print axioms InitECandidate.Solver.Input.SourceEntry.terminating_execution
#print axioms InitECandidate.Solver.Input.SourceEntry.original_main
