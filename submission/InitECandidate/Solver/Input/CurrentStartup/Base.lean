import InitECandidate.Solver.Input.CurrentStartup.Code
import InitECandidate.Solver.Input.GlobalByteEffects
import InitECandidate.Solver.Input.GlobalEffectsGlobalCall
import InitECandidate.Solver.Input.GlobalEffectsScoped

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

inductive Cursor where | scratch | frame

def key : Cursor → MlS
  | .scratch => ofString "scratch_ptr"
  | .frame => ofString "frame_mem_ptr"

end InitECandidate.Solver.Input.CurrentStartup
