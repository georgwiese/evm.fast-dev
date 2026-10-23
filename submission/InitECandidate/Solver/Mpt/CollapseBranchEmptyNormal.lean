import InitECandidate.Solver.Mpt.CollapseBranchSuffixProgram
import InitECandidate.Solver.Mpt.DeleteExtensionTailArguments
import InitECandidate.Solver.Mpt.LeafConstructorTail
import InitECandidate.Solver.Mpt.LeafConstructorPathGraph
import InitECandidate.Solver.Mpt.Fail
import InitECandidate.Solver.Input.SequenceReturned

namespace InitECandidate.Solver.Mpt.CollapseBranch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem empty_guard_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (length : BitVec 64)
    (cell : source.locals.lookup (ofString "vl")=some (.val (.word length))) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source emptyGuard=(none,target)) : target=source ∧ length≠0#64 := by
  by_cases zero : length=0#64
  · have selected : evaluateHOLFiniteState source emptyGuard=evaluateHOLFiniteState source (.call (some (none,none)) (ofString "mpt_fail") [.const 12#64]):=by
      rw [value_shapes.2.2.2.2.1,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,localVar,cell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    exact (Fail.call_not_normal source target installed _ (selected.symm.trans normal)).elim
  · have skipped : evaluateHOLFiniteState source emptyGuard=(none,source):=by
      rw [value_shapes.2.2.2.2.1,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,localVar,cell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
    exact ⟨congrArg Prod.snd (normal.symm.trans skipped),zero⟩

/-- The actual zero-child collapse turns the existing branch value into
a genuine fresh leaf with a zero-length path. Its path pointer is the old
node, exactly as in the original program; no bytes are read or aliased. -/
theorem empty_paths (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap node : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (pathFloor : pathLower≤nodeLower) (floor : nodeLower≤heap.toNat)
    (member : graph.valid node) (active : node≠0#64) (tag : wordAt source.memory node=3#64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (valueCell : source.locals.lookup (ofString "vl")=some (.val (.word (wordAt source.memory (node+168#64)))))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0) (domain : source.memaddrs=InitE.ordinaryDomain)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source emptyBlock=(some (.returned value),target)) :
    value=.val (.word heap) ∧ source.clock-target.clock≤3 ∧ target.code=source.code ∧
      NodeConstructor.Physical .leaf source target heap (NodeConstructor.leafWords node 0#64 (wordAt source.memory (node+160#64)) (wordAt source.memory (node+168#64))) ∧
      ∃ next : TrieWalk.Graph target.memory target.memaddrs,(∀ current,next.valid current ↔ graph.valid current ∨ current=heap) ∧ next.valid heap ∧
        next.Regions nodeLower (PersistentAlloc.rounded heap 64#64).toNat ∧ next.Disjoint ∧ Nonempty (TrieWalk.Values next limit property) ∧
        next.PathBytes target.be ∧ next.PathRegions pathLower (PersistentAlloc.rounded heap 64#64).toNat ∧ next.PathSeparated := by
  have notHash : wordAt source.memory node≠0#64:=by rw [tag]; decide
  have notLeaf : wordAt source.memory node≠1#64:=by rw [tag]; decide
  have notExtension : wordAt source.memory node≠2#64:=by rw [tag]; decide
  let data:=values.branch node member active notHash notLeaf notExtension
  have pointer : wordAt source.memory (node+160#64)=data.pointer:=by simp [wordAt,data.pointerStored,MemoryBytes.wordBits]
  have length : wordAt source.memory (node+168#64)=data.length:=by simp [wordAt,data.lengthStored,MemoryBytes.wordBits]
  have safe : Input.LocalPrefix (ofString "node") emptyGuard:=by
    rw [value_shapes.2.2.2.2.1]
    exact .ite _ (.call none _ _ (by intro name impossible; cases impossible)) .skip
  rw [value_shapes.2.2.2.1] at normal
  obtain ⟨middle,guardRun,leafRun⟩:=Input.sequence_returned source target emptyGuard emptyLeaf value
    (fun returned=>(safe.summary_full source).2.1 returned) normal
  obtain ⟨same,_nonempty⟩:=empty_guard_normal source middle _ valueCell installed guardRun
  subst middle
  have ptrRead : eval source (field "node" 160#64)=some (.val (.word data.pointer)):=by
    simpa only [field,DeleteExtension.field] using DeleteExtension.field_read source "node" node 160#64 data.pointer nodeCell data.pointerMapped data.pointerStored
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) emptyArguments=
      some [.val (.word node),.val (.word 0#64),.val (.word data.pointer),.val (.word data.length)]:=by
    have ptrExact:=ptrRead
    simp only [eval] at ptrExact
    rw [length] at valueCell
    simp only [emptyArguments,evalListHOLFinite,evalListHOLExact,ptrExact]
    simp [evalHOLExact,toExact,localVar,nodeCell,valueCell]
  rw [value_shapes.2.2.2.2.2.1] at leafRun
  obtain ⟨answer,physical,code,price⟩:=NodeConstructor.leaf_tail_physical source target heap node 0#64 data.pointer data.length emptyArguments args domain heapCell frontier aligned installed value leafRun
  have buffer : graph.PathBuffer source.be pathLower heap.toNat node 0:=by
    refine ⟨⟨by simpa only [Nat.add_zero] using node.isLt,?_,?_⟩,?_,?_⟩
    · intro offset impossible; omega
    · intro offset impossible; omega
    · have bounded:=regions node member active
      have size:=TrieWalk.nodeBytes_bounds (wordAt source.memory node)
      exact ⟨pathFloor.trans bounded.1,by omega⟩
    · intro offset impossible; omega
  have registered:=physical.leaf_path_graph source target heap (NodeConstructor.leafWords node 0#64 data.pointer data.length) domain aligned graph limit nodeLower pathLower property
    values regions disjoint paths pathRegions separated floor (by simpa [NodeConstructor.leafWords] using buffer)
      (by simpa [NodeConstructor.leafWords] using data.payload) (by simpa [NodeConstructor.leafWords] using data.extra)
  rw [pointer,length]
  exact ⟨answer,price,code,physical,registered⟩

end InitECandidate.Solver.Mpt.CollapseBranch

#print axioms InitECandidate.Solver.Mpt.CollapseBranch.empty_guard_normal
#print axioms InitECandidate.Solver.Mpt.CollapseBranch.empty_paths
