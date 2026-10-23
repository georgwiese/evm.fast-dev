import InitECandidate.Solver.Mpt.CollapseBranchDispatch
import InitECandidate.Solver.Mpt.CollapseBranchValueEntry
import InitECandidate.Solver.Mpt.CollapseBranchValueModel
import InitECandidate.Solver.Mpt.CollapseBranchSingleCost

namespace InitECandidate.Solver.Mpt.CollapseBranch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- All actual collapse choices after the real scan and vl binding.
Failed zero-child construction and hash/allocator errors are included. -/
theorem choices_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap node : BitVec 64) (model : ScanModel source node)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower maximum : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated) (pathLimit : graph.PathLimit maximum)
    (lower : pathLower≤heap.toNat) (floor : 2701131776≤pathLower)
    (member : graph.valid node) (active : node≠0#64) (tag : wordAt source.memory node=3#64)
    (valueCell : source.locals.lookup (ofString "vl")=some (.val (.word (wordAt source.memory (node+168#64)))))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (little : source.be=false) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterValue).2.clock≤maximum/8+23 := by
  rw [after_value_dispatch source model.count _ model.countCell valueCell]
  by_cases empty : model.count=0#64
  · rw [if_pos empty]
    have price:=empty_price source.code installed source rfl
    omega
  · rw [if_neg empty]
    by_cases single : model.count=1#64 ∧ wordAt source.memory (node+168#64)=0#64
    · rw [if_pos single]
      have positiveCount : model.count≠0#64:=by rw [single.1]; decide
      exact single_cost source heap node model.selectedIndex graph limit nodeLower pathLower maximum property values regions disjoint paths pathRegions separated pathLimit lower floor member active tag
        model.nodeCell model.indexCell model.indexBound (model.selectedNonzero positiveCount) heapCell frontier aligned little domain installed
    · rw [if_neg single,value_shapes.2.2.2.2.2.2.2.2]
      have price:=Input.ClockCost.returned source.code (localVar "node") source rfl
      omega

/-- The real stored branch value is loaded and bound without a source
clock. Its actual current scan model is retained for all choice outcomes. -/
theorem value_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap node : BitVec 64) (model : ScanModel source node)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower maximum : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated) (pathLimit : graph.PathLimit maximum)
    (lower : pathLower≤heap.toNat) (floor : 2701131776≤pathLower)
    (member : graph.valid node) (active : node≠0#64) (tag : wordAt source.memory node=3#64)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (little : source.be=false) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterScan).2.clock≤maximum/8+23 := by
  let data:=values.branch node member active (by rw [tag]; decide) (by rw [tag]; decide) (by rw [tag]; decide)
  have stored : source.memory (node+168#64)=.word (wordAt source.memory (node+168#64)):=by simp only [wordAt,data.lengthStored,MemoryBytes.wordBits]
  have read : eval source (field "node" 168#64)=some (.val (.word (wordAt source.memory (node+168#64)))):=by
    simpa only [field,DeleteExtension.field] using DeleteExtension.field_read source "node" node 168#64 _ model.nodeCell data.lengthMapped stored
  let entered:=QueryBranch.bind source "vl" (wordAt source.memory (node+168#64))
  let nextModel:=model.with_value source node (wordAt source.memory (node+168#64))
  have valueCell : entered.locals.lookup (ofString "vl")=some (.val (.word (wordAt entered.memory (node+168#64)))):=bind_lookup_same _ _ _
  have price:=choices_cost entered heap node nextModel graph limit nodeLower pathLower maximum property values regions disjoint paths pathRegions separated pathLimit lower floor member active tag
    valueCell heapCell frontier aligned little domain installed
  rw [value_shapes.1]
  exact Input.ClockCost.declared_current source "vl" (field "node" 168#64) (wordAt source.memory (node+168#64)) afterValue _ read price

end InitECandidate.Solver.Mpt.CollapseBranch

#print axioms InitECandidate.Solver.Mpt.CollapseBranch.choices_cost
#print axioms InitECandidate.Solver.Mpt.CollapseBranch.value_cost
