import InitECandidate.Solver.Input.PackBytesEnvironment
import InitECandidate.Solver.Input.PackBytesBodyCost
import InitECandidate.Solver.Input.PackBytesNormal

namespace InitECandidate.Solver.Input.PackBytes
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Original two-word ABI and actual caller price for byte packing, including
allocator/copy/unaligned padding and all observed non-timeout failures. -/
theorem call_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor : BitVec 64) (n : Nat)
    (small : n≤134217728) (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (inputArena : AllocatedBytes.Arena p n) (arena : AllocatedBytes.Arena cursor (padded n)) (aligned : cursor.toNat%8=0)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values p n))
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "pack_bytes") arguments)=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤n/8+73 := by
  obtain ⟨callee,called,pLocal,nLocal⟩ := environment source.code.lookup p n (original_code source.code installed)
  exact ClockCost.call_current_terminating source post destination (ofString "pack_bytes") arguments (values p n) body callee returnShape (n/8+72) args called
    (fun result target actual notTimeout=>body_cost (callEntryStateHOLFinite source callee) target p cursor n small installed domain pLocal nLocal heap inputArena arena aligned result actual notTimeout)
    result run notTimeout

end InitECandidate.Solver.Input.PackBytes

#print axioms InitECandidate.Solver.Input.PackBytes.environment
#print axioms InitECandidate.Solver.Input.PackBytes.call_cost
