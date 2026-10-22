import InitECandidate.Solver.Mpt.NodeInvalidate
import InitECandidate.Solver.Input.IgnoredCallTarget

namespace InitECandidate.Solver.Mpt.NodeInvalidate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The actual original ignored invalidation caller reinstalls precisely
the saved locals, changes only its three cache cells and pays one call tick. -/
theorem call_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word node)])
    (installed : Input.OriginalCode.Installed source.code)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena node 32) (aligned : node.toNat%8=0)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "node_invalidate") arguments)=(none,target)) :
    target={post source node with clock:=source.clock-1} := by
  obtain ⟨callee,called,nd⟩:=Input.word_environment source.code.lookup (ofString "node_invalidate") (ofString "nd") body .one node
    (original_code source.code installed)
  have child:=execute (callEntryStateHOLFinite source callee) node nd domain arena aligned
  have actual:=Input.CallNormal.ignored_target source target (ofString "node_invalidate") arguments [.val (.word node)] body callee .one
    args called (.val (.word 0#64)) _ child normal
  rw [actual]
  rfl

end InitECandidate.Solver.Mpt.NodeInvalidate

#print axioms InitECandidate.Solver.Mpt.NodeInvalidate.call_normal
