import InitECandidate.Solver.Mpt.NodeConstructorScopedNone
import InitECandidate.Solver.Mpt.ExtensionConstructorTail

namespace InitECandidate.Solver.Mpt.NodeConstructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Actual falling-through extension construction with its real scalar
ABI, allocation and exact following caller state. -/
theorem extension_scoped_none_physical (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap key length child : BitVec 64)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word key),.val (.word length),.val (.word child)])
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "node_new_ext") arguments continuation)=(none,post)) :
    1≤source.clock ∧ ∃ ready inner,
      ready.locals.lookup (ofString name)=some (.val (.word heap)) ∧ ready.locals=source.locals.update (ofString name,.val (.word heap)) ∧
      Physical .extension source ready heap (extensionWords key length child) ∧ ready.code=source.code ∧
      evaluateHOLFiniteState ready continuation=(none,inner) ∧ post=QueryBranch.restore source name inner := by
  obtain ⟨callee,called,nib,nlen,childCell⟩:=Input.word_triple_environment source.code.lookup (ofString "node_new_ext")
    (ofString "nib") (ofString "nlen") (ofString "child") (body .extension) .one key length child (by decide) (by decide) (by decide)
    (original_code .extension source.code installed)
  have inputs : Inputs .extension (callEntryStateHOLFinite source callee) (extensionWords key length child):=by
    simpa only [Inputs,extensionWords,callEntryStateHOLFinite,ite_true,ite_false,show ("nlen" : String)≠"nib" from by decide,
      show ("child" : String)≠"nib" from by decide,show ("child" : String)≠"nlen" from by decide] using And.intro nib (And.intro nlen childCell)
  exact scalar_scoped_none_physical .extension (by decide) source post heap (extensionWords key length child) name arguments _ callee continuation args called inputs
    domain heapCell frontier aligned installed normal

end InitECandidate.Solver.Mpt.NodeConstructor

#print axioms InitECandidate.Solver.Mpt.NodeConstructor.extension_scoped_none_physical
