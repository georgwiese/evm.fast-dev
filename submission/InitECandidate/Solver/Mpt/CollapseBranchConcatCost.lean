import InitECandidate.Solver.Mpt.CollapseBranchConcatEntry
import InitECandidate.Solver.Mpt.CollapseBranchSuffixCost
import InitECandidate.Solver.Input.ClockCostCurrentScoped

namespace InitECandidate.Solver.Mpt.CollapseBranch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Every actual cat/constructor outcome, with no later allocation or
graph-success premise. The one selected nibble has no whole-word charge. -/
theorem concat_scope_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap nibble child : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (pathLower : Nat) (pathRegions : graph.PathRegions pathLower heap.toNat)
    (buffer : graph.PathBuffer source.be pathLower heap.toNat nibble 1) (floor : 2701131776≤pathLower)
    (member : graph.valid child) (active : child≠0#64) (tag : wordAt source.memory child=1#64 ∨ wordAt source.memory child=2#64)
    (nibbleCell : source.locals.lookup (ofString "nib")=some (.val (.word nibble)))
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source concatScope).2.clock≤(wordAt source.memory (child+40#64)).toNat/8+22 := by
  let pointer:=wordAt source.memory (child+32#64)
  let childLength:=wordAt source.memory (child+40#64)
  have rightBounds:=pathRegions child member active tag
  change pathLower≤pointer.toNat ∧ pointer.toNat+childLength.toNat≤heap.toNat at rightBounds
  have sourceA : AllocatedBytes.Arena nibble 1:=⟨floor.trans buffer.bounds.1,by have before:=buffer.bounds.2; have upper:=frontier.upper; omega⟩
  have sourceB : AllocatedBytes.Arena pointer childLength.toNat:=⟨floor.trans rightBounds.1,by have before:=rightBounds.2; have upper:=frontier.upper; omega⟩
  have args:=concat_arguments source nibble child graph member active tag nibbleCell childCell
  obtain ⟨callee,called,aCell,alCell,bCell,blCell⟩:=NibblesConcat.environment source nibble 1#64 pointer childLength (NibblesConcat.original_code source.code installed)
  have price : (callEntryStateHOLFinite source callee).clock-(evaluateHOLFiniteState (callEntryStateHOLFinite source callee) NibblesConcat.body).2.clock≤childLength.toNat/8+18:=by
    simpa only [show (1#64).toNat=1 from rfl,show (1/8 : Nat)=0 from rfl,Nat.zero_add] using
      NibblesConcat.body_cost (callEntryStateHOLFinite source callee) heap nibble 1#64 pointer childLength sourceA sourceB aCell alCell bCell blCell heapCell frontier domain installed
  rw [merge_shapes.2.2.1]
  have whole:=Input.ClockCost.scoped_current source (ofString "cat") .one (ofString "nibbles_concat") concatArguments (NibblesConcat.callValues nibble 1#64 pointer childLength)
    NibblesConcat.body afterConcat callee .one (childLength.toNat/8+18) 3 args called price (constructor_price source.code installed)
  change source.clock-(evaluateHOLFiniteState source (.decCall (ofString "cat") .one (ofString "nibbles_concat") concatArguments afterConcat)).2.clock≤childLength.toNat/8+22
  omega

end InitECandidate.Solver.Mpt.CollapseBranch

#print axioms InitECandidate.Solver.Mpt.CollapseBranch.concat_scope_cost
