import InitECandidate.Solver.Mpt.NodeConstructorAssigned
import InitECandidate.Solver.Input.WordQuadEnvironment

namespace InitECandidate.Solver.Mpt.NodeConstructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def leafWords (nibbles length pointer size : BitVec 64) (name : String) : BitVec 64:=
  if name="nib" then nibbles else if name="nlen" then length else if name="vptr" then pointer else size

/-- Original node_new_leaf at its actual assigned caller, deriving its
fresh64-byte allocation and all original leaf fields from the real ABI. -/
theorem leaf_assigned (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap nibbles length pointer size : BitVec 64)
    (name : MlS) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some [.val (.word nibbles),.val (.word length),.val (.word pointer),.val (.word size)])
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,name),none)) (ofString "node_new_leaf") arguments)=(none,target)) :
    AllocatedBytes.Arena heap 64 ∧ target=setVarHOLFinite name (.val (.word heap))
      {PersistentAlloc.post {source with clock:=source.clock-2} heap 64#64 with
        memory:=WordWrites.write source.memory (FieldStores.writes heap (fields .leaf (leafWords nibbles length pointer size)))} := by
  obtain ⟨callee,called,nib,nlen,vptr,vlen⟩:=Input.word_quad_environment source.code.lookup (ofString "node_new_leaf")
    (ofString "nib") (ofString "nlen") (ofString "vptr") (ofString "vlen") (body .leaf) .one nibbles length pointer size
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (original_code .leaf source.code installed)
  have inputs : Inputs .leaf (callEntryStateHOLFinite source callee) (leafWords nibbles length pointer size):=by
    simpa only [Inputs,leafWords,callEntryStateHOLFinite,ite_true,ite_false,show ("nlen" : String)≠"nib" from by decide,
      show ("vptr" : String)≠"nib" from by decide,show ("vptr" : String)≠"nlen" from by decide,
      show ("vlen" : String)≠"nib" from by decide,show ("vlen" : String)≠"nlen" from by decide,
      show ("vlen" : String)≠"vptr" from by decide] using And.intro nib (And.intro nlen (And.intro vptr vlen))
  exact assigned_normal .leaf (by decide) source target heap (leafWords nibbles length pointer size) name arguments _ callee args called inputs
    domain heapCell frontier aligned installed normal

end InitECandidate.Solver.Mpt.NodeConstructor

#print axioms InitECandidate.Solver.Mpt.NodeConstructor.leaf_assigned
