import InitECandidate.Solver.Input.CurrentHash.Code
import InitECandidate.Solver.Input.LoopBodyEffects
import InitECandidate.Solver.Input.GlobalEffectsCall

namespace InitECandidate.Solver.Input.CurrentHash.MemoryGlobals
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

inductive Kind where | copy | zero
def routine : Kind → Code.Routine | .copy => .memcpy | .zero => .memzero

set_option maxRecDepth 100000 in
theorem supported (kind : Kind) : LoopBodyEffects.accepts (Code.body (routine kind)) = true := by
  cases kind <;> simp only [routine,Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_memcpy,Guest.Software.guestFn_memzero,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_none]
  all_goals rfl

/-- Both actual buffer routines preserve every global on every outcome,
including their heap cursor. No mapping or successful stores are required. -/
theorem body (kind : Kind) (key : MlS) (code) : GlobalEffects.Preserves key code (Code.body (routine kind)) :=
  LoopBodyEffects.sound key code (Code.body (routine kind)) (supported kind)

theorem call (kind : Kind) (key : MlS) (code) (installed : OriginalCode.Installed code)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) :
    GlobalEffects.Preserves key code (.call (LocalEffects.callInfo destination) (Code.name (routine kind)) arguments) :=
  GlobalEffects.call_body key code destination (Code.name (routine kind)) arguments
    (Code.formals (routine kind)) (Code.body (routine kind)) (Code.shape (routine kind))
    (Code.installed code installed (routine kind)) (body kind key code)

end InitECandidate.Solver.Input.CurrentHash.MemoryGlobals

#print axioms InitECandidate.Solver.Input.CurrentHash.MemoryGlobals.supported
#print axioms InitECandidate.Solver.Input.CurrentHash.MemoryGlobals.body
#print axioms InitECandidate.Solver.Input.CurrentHash.MemoryGlobals.call
