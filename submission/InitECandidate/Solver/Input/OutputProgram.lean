import InitECandidate.Solver.Input.SharedStoreLocal
import InitECandidate.Solver.Input.CounterLoopCost
import InitECandidate.Solver.Input.QuietClockEffects
import InitECandidate.Solver.Input.ClockCostCurrent
import InitECandidate.Solver.Input.MemoryWordCalls

namespace InitECandidate.Solver.Input.Output
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_output_write with | .function fn => progToHOL fn.body | _ => .skip
def test : ExpHOL 64 := .cmp .lower (localVar "i") (localVar "n")
def destination : ExpHOL 64 := .op .add [.const 2688614400#64,localVar "i"]
def loaded : ExpHOL 64 := .loadByte (.op .add [localVar "src",localVar "i"])
def increment : ProgHOL 64 := .assign .local (ofString "i") (.op .add [localVar "i",.const 1#64])
def step : ProgHOL 64 := .seq (.shMemStore .op8 destination loaded) increment
def loop : ProgHOL 64 := .while test step
def formals : List (MlS × ShapeHOL) := [(ofString "src",.one),(ofString "n",.one)]

theorem original_shape : body = .dec (ofString "i") .one (.const 0#64) (.seq loop (.return (.const 0#64))) := by
  simp only [body,Guest.guestFn_output_write,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    loop,test,step,destination,loaded,increment,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "output_write") = some (formals,body,.one) := by
  have checked := OriginalCode.indexed code installed 25 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_output_write) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.guestFn_output_write,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem step_cost (code) : ClockCost.Bound code step 0 := by
  have shared := ClockCost.of_quiet code _ (QuietClock.shared_store code .op8 destination loaded)
  have assign := ClockCost.assign code (ofString "i") (.op .add [localVar "i",.const 1#64])
  exact ClockCost.sequence code _ _ 0 0 shared assign

theorem step_summary {F : Type} (source : PanSemStateFiniteExact 64 F) : LocalSummary (ofString "n") step source :=
  local_summary_sequence (ofString "n") _ _ (shared_store_local (ofString "n") .op8 destination loaded)
    (fun state => (LocalPrefix.assign (ofString "i") (.op .add [localVar "i",.const 1#64]) (by decide)).summary_full state) source

theorem step_advances : CounterFlow.Advances (ofString "i") 1 step := by
  intro source post word cell run
  obtain ⟨middle,stored,assigned⟩ := sequence_none source post _ _ run
  have info := shared_store_local (ofString "i") .op8 destination loaded source
  unfold LocalSummary at info
  rw [stored] at info
  exact CounterFlow.increment (ofString "i") middle post word ((info.1 rfl).trans cell) assigned

end InitECandidate.Solver.Input.Output

#print axioms InitECandidate.Solver.Input.Output.original_shape
#print axioms InitECandidate.Solver.Input.Output.original_code
#print axioms InitECandidate.Solver.Input.Output.step_cost
#print axioms InitECandidate.Solver.Input.Output.step_summary
#print axioms InitECandidate.Solver.Input.Output.step_advances
