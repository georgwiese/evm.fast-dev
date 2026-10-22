import InitECandidate.Solver.Mpt.StateInitStorageNormal
import InitECandidate.Solver.Mpt.StateInitPrefixFields

namespace InitECandidate.Solver.Mpt.StateInit
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessCore.Stack

/-- Actual original40-byte WitnessPreState, including its constructed
database pointers, decoded root and physical storage-root cache table. -/
structure WorkspaceView (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (workspace nodes rootHash codes root storageTable : BitVec 64) : Prop where
  arena : AllocatedBytes.Arena workspace 40
  aligned : workspace.toNat%8=0
  pointer : source.globals.lookup (ofString "ws")=some (.val (.word workspace))
  nodeDatabase : source.memory workspace=.word nodes
  rootHash : source.memory (workspace+8#64)=.word rootHash
  codeDatabase : source.memory (workspace+16#64)=.word codes
  root : source.memory (workspace+24#64)=.word root
  storageTable : source.memory (workspace+32#64)=.word storageTable

theorem WorkspaceView.before_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (workspace nodes rootHash codes root storageTable : BitVec 64) (cursor : Nat)
    (view : WorkspaceView source workspace nodes rootHash codes root storageTable) (before : workspace.toNat+40≤cursor)
    (pointer : target.globals.lookup (ofString "ws")=some (.val (.word workspace)))
    (memory : ∀ query : BitVec 64,query.toNat<cursor → target.memory query=source.memory query) :
    WorkspaceView target workspace nodes rootHash codes root storageTable := by
  have bounded (offset : Nat) (inside : offset<40) : (workspace+BitVec.ofNat 64 offset).toNat<cursor:=by
    have numeric:=byteAddress_toNat workspace offset (by have upper:=view.arena.upper; omega)
    change (workspace+BitVec.ofNat 64 offset).toNat=workspace.toNat+offset at numeric
    omega
  exact ⟨view.arena,view.aligned,pointer,(memory workspace (by omega)).trans view.nodeDatabase,
    (memory _ (bounded 8 (by decide))).trans view.rootHash,(memory _ (bounded 16 (by decide))).trans view.codeDatabase,
    (memory _ (bounded 24 (by decide))).trans view.root,(memory _ (bounded 32 (by decide))).trans view.storageTable⟩

/-- The same actually executed root/cache states establish every workspace
word, with input fields retained through materialization and the genuine
decoded root/table pointers installed by their real stores. -/
theorem workspace_of_storage (source current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (workspace nodes rootHash codes root storageHeap : BitVec 64) (frontier : Nat)
    (arena : AllocatedBytes.Arena workspace 40) (aligned : workspace.toNat%8=0) (lower : 2713717616≤workspace.toNat)
    (workspaceCell : current.globals.lookup (ofString "ws")=some (.val (.word workspace)))
    (before : workspace.toNat+40≤frontier) (frontierBefore : frontier≤storageHeap.toNat)
    (memory : StablePrefix (ready source workspace nodes rootHash codes) current frontier)
    (valid : NaturalLayout.Valid .word (NaturalLayout.fresh .word storageHeap.toNat 64)) :
    WorkspaceView (storageReady (installedRoot current workspace root) workspace storageHeap) workspace nodes rootHash codes root storageHeap := by
  let rooted:=installedRoot current workspace root
  let target:=storageReady rooted workspace storageHeap
  have number (offset : Nat) (inside : offset<40) : (byteAddress workspace offset).toNat=workspace.toNat+offset:=
    byteAddress_toNat workspace offset (by have upper:=arena.upper; omega)
  have different (first second : Nat) (firstInside : first<40) (secondInside : second<40) (unequal : first≠second) :
      byteAddress workspace first≠byteAddress workspace second:=by
    intro equal
    have numeric:=congrArg BitVec.toNat equal
    rw [number first firstInside,number second secondInside] at numeric
    omega
  have keep (offset : Nat) (inside : offset<40) : current.memory (byteAddress workspace offset)=(ready source workspace nodes rootHash codes).memory (byteAddress workspace offset):=by
    apply memory
    · rw [number offset inside]; omega
    · rw [number offset inside]; omega
  have old (offset : Nat) (inside : offset<24) : target.memory (byteAddress workspace offset)=current.memory (byteAddress workspace offset):=by
    have away32 : byteAddress workspace offset≠workspace+32#64:=different offset 32 (by omega) (by decide) (by omega)
    have away24 : byteAddress workspace offset≠workspace+24#64:=different offset 24 (by omega) (by decide) (by omega)
    have queryBefore : (byteAddress workspace offset).toNat<storageHeap.toNat:=by rw [number offset (by omega)]; omega
    change StoreWord.put (TableRuntime.callState rooted "t" .word storageHeap.toNat 64).memory (workspace+32#64) storageHeap (byteAddress workspace offset)=_
    rw [StoreWord.put,if_neg away32,TableRuntime.caller_memory_away rooted "t" .word storageHeap.toNat 64 valid _ (Or.inl queryBefore)]
    exact if_neg away24
  have initial:=ready_cells source workspace nodes rootHash codes arena
  have nodeCell : target.memory workspace=.word nodes:=by
    have retained : target.memory workspace=(ready source workspace nodes rootHash codes).memory workspace:=by
      simpa [byteAddress] using (old 0 (by decide)).trans (keep 0 (by decide))
    exact retained.trans initial.1
  have hashCell : target.memory (workspace+8#64)=.word rootHash:=
    ((old 8 (by decide)).trans (keep 8 (by decide))).trans initial.2.1
  have codeCell : target.memory (workspace+16#64)=.word codes:=
    ((old 16 (by decide)).trans (keep 16 (by decide))).trans initial.2.2
  have rootCell : target.memory (workspace+24#64)=.word root:=by
    have away : workspace+24#64≠workspace+32#64:=different 24 32 (by decide) (by decide) (by decide)
    have queryBefore : (workspace+24#64).toNat<storageHeap.toNat:=by
      change (byteAddress workspace 24).toNat<storageHeap.toNat
      rw [number 24 (by decide)]; omega
    change StoreWord.put (TableRuntime.callState rooted "t" .word storageHeap.toNat 64).memory (workspace+32#64) storageHeap (workspace+24#64)=_
    rw [StoreWord.put,if_neg away,TableRuntime.caller_memory_away rooted "t" .word storageHeap.toNat 64 valid _ (Or.inl queryBefore)]
    simp [rooted,installedRoot,StoreWord.put]
  have tableCell : target.memory (workspace+32#64)=.word storageHeap:=by simp [target,storageReady,written,StoreWord.put]
  have pointer : target.globals.lookup (ofString "ws")=some (.val (.word workspace)):=by
    simpa [target,storageReady,written,TableRuntime.callState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
      rooted,installedRoot,show ofString "heap_ptr"≠ofString "ws" from by decide] using workspaceCell
  exact ⟨arena,aligned,pointer,nodeCell,hashCell,codeCell,rootCell,tableCell⟩

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.WorkspaceView.before_frame
#print axioms InitECandidate.Solver.Mpt.StateInit.workspace_of_storage
