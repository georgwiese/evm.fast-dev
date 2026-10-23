import InitECandidate.Solver.Mpt.LeafConstructorCall
import InitECandidate.Solver.Mpt.NodeConstructorTail

namespace InitECandidate.Solver.Mpt.NodeConstructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Original leaf tail call with the genuine four-word ABI. The actual
normal execution derives the returned allocation and every initialized
field; no later successful constructor is assumed. -/
theorem leaf_tail_physical (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap key length pointer size : BitVec 64)
    (arguments : List (ExpHOL 64))
    (argsRead : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word key),.val (.word length),.val (.word pointer),.val (.word size)])
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.call none (ofString "node_new_leaf") arguments)=(some (.returned value),post)) :
    value=.val (.word heap) ∧ Physical .leaf source post heap (leafWords key length pointer size) ∧ post.code=source.code ∧ source.clock-post.clock≤3 := by
  obtain ⟨callee,called,nib,nlen,vptr,vlen⟩:=Input.word_quad_environment source.code.lookup (ofString "node_new_leaf")
    (ofString "nib") (ofString "nlen") (ofString "vptr") (ofString "vlen") (body .leaf) .one key length pointer size
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (original_code .leaf source.code installed)
  have inputs : Inputs .leaf (callEntryStateHOLFinite source callee) (leafWords key length pointer size):=by
    simpa only [Inputs,leafWords,callEntryStateHOLFinite,ite_true,ite_false,show ("nlen" : String)≠"nib" from by decide,
      show ("vptr" : String)≠"nib" from by decide,show ("vptr" : String)≠"nlen" from by decide,
      show ("vlen" : String)≠"nib" from by decide,show ("vlen" : String)≠"nlen" from by decide,
      show ("vlen" : String)≠"vptr" from by decide] using And.intro nib (And.intro nlen (And.intro vptr vlen))
  exact scalar_tail_physical .leaf (by decide) source post heap (leafWords key length pointer size) arguments _ callee argsRead called inputs
    domain heapCell frontier aligned installed value normal

end InitECandidate.Solver.Mpt.NodeConstructor

#print axioms InitECandidate.Solver.Mpt.NodeConstructor.leaf_tail_physical
