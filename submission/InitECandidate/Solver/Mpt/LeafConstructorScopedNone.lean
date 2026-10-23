import InitECandidate.Solver.Mpt.NodeConstructorScopedNone
import InitECandidate.Solver.Mpt.LeafConstructorCall

namespace InitECandidate.Solver.Mpt.NodeConstructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The true scalar leaf ABI and actual falling-through scoped call,
retaining its physical construction and exact following caller state. -/
theorem leaf_scoped_none_physical (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap nibbles length pointer size : BitVec 64)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word nibbles),.val (.word length),.val (.word pointer),.val (.word size)])
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "node_new_leaf") arguments continuation)=(none,post)) :
    1≤source.clock ∧ ∃ ready inner,
      ready.locals.lookup (ofString name)=some (.val (.word heap)) ∧ ready.locals=source.locals.update (ofString name,.val (.word heap)) ∧ Physical .leaf source ready heap (leafWords nibbles length pointer size) ∧ ready.code=source.code ∧
      evaluateHOLFiniteState ready continuation=(none,inner) ∧ post=QueryBranch.restore source name inner := by
  obtain ⟨callee,called,nib,nlen,vptr,vlen⟩:=Input.word_quad_environment source.code.lookup (ofString "node_new_leaf")
    (ofString "nib") (ofString "nlen") (ofString "vptr") (ofString "vlen") (body .leaf) .one nibbles length pointer size
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (original_code .leaf source.code installed)
  have inputs : Inputs .leaf (callEntryStateHOLFinite source callee) (leafWords nibbles length pointer size):=by
    simpa only [Inputs,leafWords,callEntryStateHOLFinite,ite_true,ite_false,show ("nlen" : String)≠"nib" from by decide,
      show ("vptr" : String)≠"nib" from by decide,show ("vptr" : String)≠"nlen" from by decide,
      show ("vlen" : String)≠"nib" from by decide,show ("vlen" : String)≠"nlen" from by decide,
      show ("vlen" : String)≠"vptr" from by decide] using And.intro nib (And.intro nlen (And.intro vptr vlen))
  exact scalar_scoped_none_physical .leaf (by decide) source post heap (leafWords nibbles length pointer size) name arguments _ callee continuation args called inputs
    domain heapCell frontier aligned installed normal

end InitECandidate.Solver.Mpt.NodeConstructor

#print axioms InitECandidate.Solver.Mpt.NodeConstructor.leaf_scoped_none_physical
