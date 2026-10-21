import InitECandidate.Solver.Input.MaterializeCoreEntry
import InitECandidate.Solver.Mpt.WitnessCoreInitial

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The actual core body supplies its initialized literal loop state with
both real databases and complete runtime. The checked ready_fields theorem
identifies the empty stack, decode mode, live go flag and actual input words. -/
theorem core_loop_ready (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (boundary : RootBoundary input source) (installed : OriginalCode.Installed source.code)
    (scalars : OriginalScalarGlobals.Scalars source.globals)
    (pCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (nCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (scratch : Rlp.Validation.Arena source 2713714688#64 2701135872#64)
    (environment : Keccak256.Environment source 2713714976#64 2713715176#64)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source Mpt.WitnessCore.body=(outcome,post)) :
    ∃ inner,
      let current:=Mpt.WitnessCore.ready source pointer length
      RootBoundary input current ∧ OriginalCode.Installed current.code ∧ OriginalScalarGlobals.Scalars current.globals ∧
      Rlp.Validation.Arena current 2713714688#64 2701135872#64 ∧ Keccak256.Environment current 2713714976#64 2713715176#64 ∧
      current.clock=source.clock ∧
      evaluateHOLFiniteState current (.seq (.while Mpt.WitnessCore.condition Mpt.WitnessCore.loopBody) Mpt.WitnessCore.footer)=(outcome,inner) ∧ post.clock=inner.clock := by
  obtain ⟨restoreStack,inner,setup,continued,endpoint,clock⟩ := Mpt.WitnessCore.initial_trace source post pointer length pCell nCell outcome run
  let current:=Mpt.WitnessCore.ready source pointer length
  have pure:=Mpt.WitnessCore.ready_erase source pointer length
  have dbSame:=Mpt.WitnessCore.ready_other source pointer length (ofString "db") (by decide)
  have data:=RootBoundary.erase_frame input source current boundary pure dbSame
  have frame:=runtime_of_entry source current pure
  have currentInstalled : OriginalCode.Installed current.code := by rw [frame.code]; exact installed
  have globals:=congrArg PanSemStateFiniteExact.globals pure
  change current.globals=source.globals at globals
  have currentScalars : OriginalScalarGlobals.Scalars current.globals := by rw [globals]; exact scalars
  exact ⟨inner,data,currentInstalled,currentScalars,frame.scratch source current _ _ scratch,frame.hash_environment source current _ _ environment,
    Mpt.WitnessCore.ready_clock source pointer length,continued,clock⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.core_loop_ready
