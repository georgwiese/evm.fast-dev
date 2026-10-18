import InitECandidate.Solver.GasBudget.RunFramesCaughtDispatch

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A genuinely executed original suffix, followed by actual caller return
or actual caught handler. Its time and physical invariants are separate. -/
def ProgramSuffixFinish (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (continuation : ProgHOL 64)
    (ready : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  (∃ inner returned, evaluateHOLFiniteState ready continuation = (some (.returned returned), inner) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner) ∨
  ∃ inner exceptionPost err,
    evaluateHOLFiniteState ready continuation = (some (.exception (ofString "EvmErr") (.val (.word err))), inner) ∧
    emptyLocalsHOLFinite exceptionPost = emptyLocalsHOLFinite inner ∧
    evaluateHOLFiniteState (bind {exceptionPost with locals := source.locals} "err" err) opcodeHandler = (none, post)

def ScopedProgramSuffixFinish (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (continuation : ProgHOL 64)
    (ready : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∃ caller endpoint, emptyLocalsHOLFinite caller = emptyLocalsHOLFinite source ∧
    emptyLocalsHOLFinite post = emptyLocalsHOLFinite endpoint ∧ ProgramSuffixFinish caller endpoint continuation ready

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.ProgramSuffixFinish
#print axioms InitECandidate.Solver.GasBudget.RunFrames.ScopedProgramSuffixFinish
