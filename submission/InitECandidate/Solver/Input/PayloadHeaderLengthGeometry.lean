import InitECandidate.Solver.Input.PayloadHeaderPhysical
import InitECandidate.Solver.Input.RlpLength.BlockNormalRoom

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The real normal block-length child derives the encoder's full space
requirement. Header/heap alignment and separation were derived by main. -/
theorem length_geometry (input : Guest.InputBlob) (origin source current target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root header : BitVec 64) (physical : PhysicalHeader input origin source current root header)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState (callEntryStateHOLFinite current callee) RlpLength.Block.body=(some (.returned value),target)) :
    HeaderEncoding.Geometry header (headerFrontier header) := by
  have bounded : (headerFrontier header).toNat≤33806089496:=by have h:=physical.frontier.arena.upper; omega
  have room:=RlpLength.Block.normal_room (callEntryStateHOLFinite current callee) target (headerFrontier header)
    physical.installed physical.frontier.cell bounded value normal
  exact ⟨physical.buffers.ommer.headerArena.lower,physical.buffers.ommer.headerAligned,physical.frontier.afterHeader,physical.frontier.aligned,room⟩

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.length_geometry
