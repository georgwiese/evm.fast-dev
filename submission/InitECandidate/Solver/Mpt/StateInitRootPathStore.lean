import InitECandidate.Solver.Mpt.StateInitRootStore
import InitECandidate.Solver.Mpt.StateInitRootPathNormal
import InitECandidate.Solver.Mpt.WitnessNodeRegistryPathStore

namespace InitECandidate.Solver.Mpt.StateInit
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessMaterialize WitnessCore

theorem install_root_paths (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db workspace root : BitVec 64)
    (output : PathOutput input frontier db source (.val (.word root)))
    (workspaceCell : source.globals.lookup (ofString "ws")=some (.val (.word workspace)))
    (rootCell : source.locals.lookup (ofString "root")=some (.val (.word root)))
    (arena : AllocatedBytes.Arena workspace 40) (aligned : workspace.toNat%8=0) (before : workspace.toNat+40≤frontier) :
    evaluateHOLFiniteState source (store 24 "root")=(none,installedRoot source workspace root) ∧
    ∃ heap,source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
      ∃ registry : NodeRegistry (installedRoot source workspace root) frontier heap db,registry.PathModel ∧ registry.graph.valid root := by
  have physical:=output.1
  obtain ⟨physicalHeap,child,valueEq,heapCell,heapArena,heapAligned,grows,scratch,frozen,owned⟩:=physical
  obtain ⟨codeArray,nodes,codes,nodeData,codeData,dbCell,nodeBefore,codeBefore⟩:=frozen
  have domain : source.memaddrs=InitE.ordinaryDomain:=nodeData.domain
  have mapped : source.memaddrs (workspace+24#64):=AllocatedBytes.word_mapped source workspace 40 24 domain arena (by decide) aligned (by decide)
  have addressRead : eval source (.op .add [.var .global (ofString "ws"),.const 24#64])=some (.val (.word (workspace+24#64))):=by
    simp [eval,evalHOLExact,evalListHOLExact,workspaceCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have valueRead : eval source (localVar "root")=some (.val (.word root)):=by simp [eval,localVar,evalHOLExact,toExact,rootCell]
  have executed:=StoreWord.execute source (.op .add [.var .global (ofString "ws"),.const 24#64]) (localVar "root") (workspace+24#64) root addressRead valueRead mapped
  obtain ⟨heap,node,nodeValue,modelHeap,registry,paths,member⟩:=output.2
  have same : node=root:=HolWordLab.word.inj (ValueHOL.val.inj nodeValue.symm)
  subst node
  have addressNumber : (workspace+24#64).toNat=workspace.toNat+24:=byteAddress_toNat workspace 24 (by have upper:=arena.upper; omega)
  obtain ⟨next,sameMembers⟩:=registry.store_below source frontier heap db (workspace+24#64) root (by rw [addressNumber]; omega)
  have nextPaths:=paths.store_below source frontier heap db (workspace+24#64) root registry next sameMembers (by rw [addressNumber]; omega)
  exact ⟨executed,heap,modelHeap,next,nextPaths,by rw [sameMembers]; exact member⟩

/-- The genuine state_init suffix continues at the exact installed-root
state, retaining its registered root before any later table construction. -/
theorem after_root_paths_normal (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db workspace root : BitVec 64)
    (output : PathOutput input frontier db source (.val (.word root)))
    (workspaceCell : source.globals.lookup (ofString "ws")=some (.val (.word workspace)))
    (rootCell : source.locals.lookup (ofString "root")=some (.val (.word root)))
    (arena : AllocatedBytes.Arena workspace 40) (aligned : workspace.toNat%8=0) (before : workspace.toNat+40≤frontier)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterRoot=(some (.returned returned),post)) :
    evaluateHOLFiniteState (installedRoot source workspace root) afterRootStore=(some (.returned returned),post) ∧
    ∃ heap,(installedRoot source workspace root).globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
      ∃ registry : NodeRegistry (installedRoot source workspace root) frontier heap db,registry.PathModel ∧ registry.graph.valid root := by
  obtain ⟨executed,registry⟩:=install_root_paths input source frontier db workspace root output workspaceCell rootCell arena aligned before
  rw [after_root_store_shape,evaluateHOLFiniteState_seq_line780,executed] at normal
  exact ⟨normal,registry⟩

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.install_root_paths
#print axioms InitECandidate.Solver.Mpt.StateInit.after_root_paths_normal
