import InitECandidate.Solver.Mpt.DeleteExtensionConcat
import InitECandidate.Solver.Mpt.DeleteExtensionSuffixCost
import InitECandidate.Solver.Input.ClockCostCurrentScoped

namespace InitECandidate.Solver.Mpt.DeleteExtension
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- All outcomes of the actual cat/cl/constructor suffix. The allocator
failure and timeout paths require no assumed future successful graph. -/
theorem concat_scope_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap child segment length : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (pathLower : Nat)
    (pathRegions : graph.PathRegions pathLower heap.toNat)
    (segmentBuffer : graph.PathBuffer source.be pathLower heap.toNat segment length.toNat) (floor : 2701131776≤pathLower)
    (member : graph.valid child) (active : child≠0#64) (tag : wordAt source.memory child=1#64 ∨ wordAt source.memory child=2#64)
    (segmentCell : source.locals.lookup (ofString "seg")=some (.val (.word segment)))
    (lengthCell : source.locals.lookup (ofString "sl")=some (.val (.word length)))
    (childCell : source.locals.lookup (ofString "nc")=some (.val (.word child)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source concatScope).2.clock≤length.toNat/8+(wordAt source.memory (child+40#64)).toNat/8+22 := by
  let pointer:=wordAt source.memory (child+32#64)
  let childLength:=wordAt source.memory (child+40#64)
  have rightBounds:=pathRegions child member active tag
  change pathLower≤pointer.toNat ∧ pointer.toNat+childLength.toNat≤heap.toNat at rightBounds
  have sourceA : AllocatedBytes.Arena segment length.toNat:=⟨floor.trans segmentBuffer.bounds.1,by have bound:=segmentBuffer.bounds.2; have upper:=frontier.upper; omega⟩
  have sourceB : AllocatedBytes.Arena pointer childLength.toNat:=⟨floor.trans rightBounds.1,by have bound:=rightBounds.2; have upper:=frontier.upper; omega⟩
  have args:=concat_arguments source child segment length graph member active tag segmentCell lengthCell childCell
  obtain ⟨callee,called,aCell,alCell,bCell,blCell⟩:=NibblesConcat.environment source segment length pointer childLength (NibblesConcat.original_code source.code installed)
  have price:=NibblesConcat.body_cost (callEntryStateHOLFinite source callee) heap segment length pointer childLength sourceA sourceB aCell alCell bCell blCell heapCell frontier domain installed
  rw [merge_shapes.2.2.1]
  have whole:=Input.ClockCost.scoped_current source (ofString "cat") .one (ofString "nibbles_concat") concatArguments (NibblesConcat.callValues segment length pointer childLength)
    NibblesConcat.body lengthScope callee .one (length.toNat/8+childLength.toNat/8+18) 3 args called price (length_price source.code installed)
  change source.clock-(evaluateHOLFiniteState source (.decCall (ofString "cat") .one (ofString "nibbles_concat") concatArguments lengthScope)).2.clock≤length.toNat/8+childLength.toNat/8+22
  omega

end InitECandidate.Solver.Mpt.DeleteExtension

#print axioms InitECandidate.Solver.Mpt.DeleteExtension.concat_scope_cost
