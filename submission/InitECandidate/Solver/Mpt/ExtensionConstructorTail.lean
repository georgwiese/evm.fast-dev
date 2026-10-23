import InitECandidate.Solver.Mpt.NodeConstructorTail
import InitECandidate.Solver.Input.WordTripleEnvironment

namespace InitECandidate.Solver.Mpt.NodeConstructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def extensionWords (key length child : BitVec 64) (name : String) : BitVec 64:=
  if name="nib" then key else if name="nlen" then length else child

/-- The original extension tail call uses the actual three-word ABI;
its result, room and physical writes follow from that real execution. -/
theorem extension_tail_physical (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap key length child : BitVec 64)
    (arguments : List (ExpHOL 64))
    (argsRead : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word key),.val (.word length),.val (.word child)])
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.call none (ofString "node_new_ext") arguments)=(some (.returned value),post)) :
    value=.val (.word heap) ∧ Physical .extension source post heap (extensionWords key length child) ∧ post.code=source.code ∧ source.clock-post.clock≤3 := by
  obtain ⟨callee,called,nib,nlen,childCell⟩:=Input.word_triple_environment source.code.lookup (ofString "node_new_ext")
    (ofString "nib") (ofString "nlen") (ofString "child") (body .extension) .one key length child (by decide) (by decide) (by decide)
    (original_code .extension source.code installed)
  have inputs : Inputs .extension (callEntryStateHOLFinite source callee) (extensionWords key length child):=by
    simpa only [Inputs,extensionWords,callEntryStateHOLFinite,ite_true,ite_false,show ("nlen" : String)≠"nib" from by decide,
      show ("child" : String)≠"nib" from by decide,show ("child" : String)≠"nlen" from by decide] using And.intro nib (And.intro nlen childCell)
  exact scalar_tail_physical .extension (by decide) source post heap (extensionWords key length child) arguments _ callee argsRead called inputs
    domain heapCell frontier aligned installed value normal

end InitECandidate.Solver.Mpt.NodeConstructor

#print axioms InitECandidate.Solver.Mpt.NodeConstructor.extension_tail_physical
