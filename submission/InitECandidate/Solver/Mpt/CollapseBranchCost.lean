import InitECandidate.Solver.Mpt.CollapseBranchValueCost
import InitECandidate.Solver.Mpt.CollapseBranchScanEntry
import InitECandidate.Solver.Mpt.TrieGraphPathErase
import InitECandidate.Solver.Input.ClockCostSequenceReached

namespace InitECandidate.Solver.Mpt.CollapseBranch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem after_counter_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap node : BitVec 64) (model : ScanModel source node)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower maximum : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated) (pathLimit : graph.PathLimit maximum)
    (lower : pathLower≤heap.toNat) (floor : 2701131776≤pathLower)
    (member : graph.valid node) (active : node≠0#64) (tag : wordAt source.memory node=3#64)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (little : source.be=false) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterCounter).2.clock≤(16-model.index.toNat)+maximum/8+23 := by
  have children (index : Nat) (inside : index<16) : ∃ child : BitVec 64,source.memaddrs (node+32#64+BitVec.ofNat 64 index*8#64) ∧
      source.memory (node+32#64+BitVec.ofNat 64 index*8#64)=.word child:=by
    let view:=graph.branch node member active (by rw [tag]; decide) (by rw [tag]; decide) (by rw [tag]; decide) index inside
    have product : BitVec.ofNat 64 (index*8)=BitVec.ofNat 64 index*8#64:=by rw [BitVec.ofNat_mul]
    exact ⟨view.child,by simpa only [product] using view.mapped,by simpa only [product] using view.stored⟩
  have front:=scan_cost source model.index model.counterCell model.bounded
  rw [setup_shapes.2.2.2]
  have price:=Input.ClockCost.sequence_reached_current source scan afterScan (16-model.index.toNat) (maximum/8+23) front (by
    intro middle normal
    obtain ⟨frame,finished,_stopped⟩:=scan_normal source middle node model children normal
    obtain ⟨current,same,currentRegions,currentDisjoint,⟨currentValues⟩,currentPaths,currentPathRegions,currentSeparated⟩:=
      graph.after_erase source middle limit nodeLower heap.toNat pathLower heap.toNat property values regions disjoint paths pathRegions separated frame
    have currentLimit:=TrieWalk.Graph.PathLimit.of_erase source middle graph current maximum pathLimit same frame
    have memory:=Input.LocalEffects.memory_of_erase source middle frame
    have globals:=congrArg PanSemStateFiniteExact.globals frame
    have sameDomain:=congrArg PanSemStateFiniteExact.memaddrs frame
    have endian:=congrArg PanSemStateFiniteExact.be frame
    have code:=congrArg PanSemStateFiniteExact.code frame
    change middle.globals=source.globals at globals
    change middle.memaddrs=source.memaddrs at sameDomain
    change middle.be=source.be at endian
    change middle.code=source.code at code
    have currentMember : current.valid node:=by rw [same]; exact member
    have currentTag : wordAt middle.memory node=3#64:=by rw [memory]; exact tag
    have currentHeap : middle.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by rw [globals]; exact heapCell
    have currentInstalled : Input.OriginalCode.Installed middle.code:=by rw [code]; exact installed
    exact value_cost middle heap node finished current limit nodeLower pathLower maximum property currentValues currentRegions currentDisjoint currentPaths currentPathRegions currentSeparated currentLimit
      lower floor currentMember active currentTag currentHeap frontier aligned (endian.trans little) (sameDomain.trans domain) currentInstalled)
  omega

/-- Every outcome of unchanged252 is bounded by the actual sixteen-child
scan and current full stored-path limit. All helper failures and timeouts
are included; normal scan/allocation states are derived only when reached. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap node : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower maximum : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated) (pathLimit : graph.PathLimit maximum)
    (lower : pathLower≤heap.toNat) (floor : 2701131776≤pathLower)
    (member : graph.valid node) (active : node≠0#64) (tag : wordAt source.memory node=3#64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (little : source.be=false) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤maximum/8+39 := by
  have priced:=after_counter_cost (setup source) heap node (initial_model source node nodeCell) graph limit nodeLower pathLower maximum property values regions disjoint paths pathRegions separated pathLimit lower floor member active tag
    heapCell frontier aligned little domain installed
  change (setup source).clock-(evaluateHOLFiniteState (setup source) afterCounter).2.clock≤16+maximum/8+23 at priced
  have tail : (setup source).clock-(evaluateHOLFiniteState (setup source) afterCounter).2.clock≤maximum/8+39:=by omega
  rw [setup_shapes.1]
  apply Input.ClockCost.declared_current source "count" (.const 0#64) 0#64 afterCount (maximum/8+39) rfl
  rw [setup_shapes.2.1]
  apply Input.ClockCost.declared_current (QueryBranch.bind source "count" 0#64) "idx" (.const 0#64) 0#64 afterIndex (maximum/8+39) rfl
  rw [setup_shapes.2.2.1]
  exact Input.ClockCost.declared_current (QueryBranch.bind (QueryBranch.bind source "count" 0#64) "idx" 0#64) "i" (.const 0#64) 0#64 afterCounter (maximum/8+39) rfl tail

end InitECandidate.Solver.Mpt.CollapseBranch

#print axioms InitECandidate.Solver.Mpt.CollapseBranch.after_counter_cost
#print axioms InitECandidate.Solver.Mpt.CollapseBranch.body_cost
