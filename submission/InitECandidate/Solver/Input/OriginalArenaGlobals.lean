import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.Input.DeclarationGlobals

namespace InitECandidate.Solver.Input.OriginalArenaGlobals
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

inductive Kind where | heap | scratch | frame

def Kind.name : Kind → MlS
  | .heap => ofString "heap_ptr"
  | .scratch => ofString "scratch_ptr"
  | .frame => ofString "frame_mem_ptr"

set_option maxRecDepth 100000 in
open scoped InitE.MetadataComputation InitE.NameComputation in
theorem checked (kind : Kind) : DeclarationCode.literalGlobalCheck kind.name OriginalCode.program = true := by
  cases kind <;> decide_cbv

set_option maxRecDepth 100000 in
open scoped InitE.MetadataComputation InitE.NameComputation in
theorem value (kind : Kind) (incoming : Option (ValueHOL 64)) :
    DeclarationCode.finalGlobal kind.name OriginalCode.program incoming = some (.val (.word 0#64)) := by
  cases kind <;> cbv

/-- The fixed declaration pass really installs all three scalar arena
globals. This is derived for any successful pass, before main executes. -/
theorem declaration_pass (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    [DecidablePred source.memaddrs]
    (run : evaluateDeclsHOLFinite source OriginalCode.program = some target) (kind : Kind) :
    target.globals.lookup kind.name = some (.val (.word 0#64)) := by
  rw [DeclarationCode.global_lookup source target OriginalCode.program kind.name
    (DeclarationCode.literal_check kind.name OriginalCode.program (checked kind)) run,value]

end InitECandidate.Solver.Input.OriginalArenaGlobals

#print axioms InitECandidate.Solver.Input.OriginalArenaGlobals.checked
#print axioms InitECandidate.Solver.Input.OriginalArenaGlobals.value
#print axioms InitECandidate.Solver.Input.OriginalArenaGlobals.declaration_pass
