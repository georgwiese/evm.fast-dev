import InitE.SourceSemantics
import InitECandidate.Solver.Input.OriginalCode

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual initialized cursors, ordinary domain and installed Software
code. Main's real declaration/mem_init/startup trace establishes these fields;
consumers of the state need no initialization implementation imports. -/
structure ArenaState (state : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  scratch : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word 2965299200#64))
  frame : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word 2952790016#64))
  domain : state.memaddrs = InitE.ordinaryDomain
  code : OriginalCode.Installed state.code

end InitECandidate.Solver.Input.CurrentStartup
