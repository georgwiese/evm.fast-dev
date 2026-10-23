import InitECandidate.Solver.Mpt.CollapseBranchAfterStoreNormal
import InitECandidate.Solver.Mpt.CollapseBranchConcatCost
import InitECandidate.Solver.Mpt.TriePathLimit

namespace InitECandidate.Solver.Mpt.CollapseBranch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

theorem after_store_price_lower (memory : Memory) (child : BitVec 64) : 3≤afterStorePrice memory child := by
  unfold afterStorePrice
  split <;> omega

theorem after_store_price_limit {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : TrieWalk.Graph memory domain) (maximum : Nat) (limit : graph.PathLimit maximum)
    (child : BitVec 64) (member : graph.valid child) (active : child≠0#64) (notHash : wordAt memory child≠0#64) :
    afterStorePrice memory child≤maximum/8+22 := by
  unfold afterStorePrice
  by_cases branch : wordAt memory child=3#64
  · rw [if_pos branch]; omega
  · rw [if_neg branch]
    have bound:=limit child member active (graph.path_kind child member active notHash branch)
    omega

/-- Every actual original post-byte-store outcome, priced at the actual
branch/path tag and full stored length. No future constructor or graph
success is needed for either alternative. -/
theorem after_store_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap nibble child : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (pathLower : Nat) (pathRegions : graph.PathRegions pathLower heap.toNat)
    (buffer : graph.PathBuffer source.be pathLower heap.toNat nibble 1) (floor : 2701131776≤pathLower)
    (member : graph.valid child) (active : child≠0#64) (notHash : wordAt source.memory child≠0#64)
    (nibbleCell : source.locals.lookup (ofString "nib")=some (.val (.word nibble)))
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (tagCell : source.locals.lookup (ofString "ck")=some (.val (.word (wordAt source.memory child))))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterStore).2.clock≤afterStorePrice source.memory child := by
  by_cases branch : wordAt source.memory child=3#64
  · rw [branch_dispatch source _ tagCell,if_pos branch]
    simpa only [NodeConstructor.name,afterStorePrice,if_pos branch] using DeleteExtension.scalar_tail_price .extension (by decide) source.code installed branchArguments source rfl
  · rw [branch_dispatch source _ tagCell,if_neg branch]
    have tag:=graph.path_kind child member active notHash branch
    simpa only [afterStorePrice,if_neg branch] using concat_scope_cost source heap nibble child graph pathLower pathRegions buffer floor member active tag
      nibbleCell childCell heapCell frontier domain installed

end InitECandidate.Solver.Mpt.CollapseBranch

#print axioms InitECandidate.Solver.Mpt.CollapseBranch.after_store_price_lower
#print axioms InitECandidate.Solver.Mpt.CollapseBranch.after_store_price_limit
#print axioms InitECandidate.Solver.Mpt.CollapseBranch.after_store_cost
