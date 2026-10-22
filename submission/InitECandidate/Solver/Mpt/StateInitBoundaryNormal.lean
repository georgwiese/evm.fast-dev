import InitECandidate.Solver.Mpt.StateInitRuntime
import InitECandidate.Solver.Mpt.StateInitCompleteTables

namespace InitECandidate.Solver.Mpt.StateInit
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.Main.RunAttemptConstructors WitnessCore

/-- Returning to arbitrary saved caller locals retains every actual
initialized workspace, trie, table and journal fact. -/
theorem Output.with_locals (input : Guest.InputBlob) (origin post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (workspace nodes rootHash codes : BitVec 64) (output : Output input origin post workspace nodes rootHash codes)
    (locals : HolFiniteMapExact Flapjack.Pancake.PanLang.MlS (ValueHOL 64)) :
    Output input origin {post with locals:=locals} workspace nodes rootHash codes:=by
  obtain ⟨installed,scalars,scratch,globals,code,domain,endian,oracle,heap,root,storage,heapCell,arena,aligned,view,frozen,table,bs,
    registry,member,regions,block,older,workspaceBefore⟩:=output
  let target:={post with locals:=locals}
  have nextScratch:=scratch.of_fields post target 2713714688#64 2701135872#64 rfl rfl
  have nextView : WorkspaceView target workspace nodes rootHash codes root storage:=
    ⟨view.arena,view.aligned,view.pointer,view.nodeDatabase,view.rootHash,view.codeDatabase,view.root,view.storageTable⟩
  have nextFrozen:=frozen.frame input (QueryBranch.bind post "db" nodes) (QueryBranch.bind target "db" nodes) workspace.toNat rfl rfl
    ((bind_lookup_same target "db" nodes).trans (bind_lookup_same post "db" nodes).symm) (by intro query lower upper; rfl)
  obtain ⟨next,same⟩:=registry.of_fields post target (PersistentAlloc.rounded workspace 40#64).toNat heap nodes rfl rfl
  have nextMember : next.graph.valid root:=by rw [same]; exact member
  have nextRegions:=regions.of_agreement post.memory target.memory post.memaddrs target.memaddrs registry.graph next.graph
    (PersistentAlloc.rounded workspace 40#64).toNat storage.toNat same (by intro node known active; rfl)
  have nextTable:=TableState.of_fields table (target:=target) rfl rfl rfl rfl
  have nextBlock:=block.of_fields post target (BitVec.ofNat 64 (NaturalLayout.freshEnd .word storage.toNat 64)) workspace rfl rfl rfl rfl
  exact ⟨installed,scalars,nextScratch,globals,code,domain,endian,oracle,heap,root,storage,heapCell,arena,aligned,nextView,nextFrozen,nextTable,bs,next,nextMember,nextRegions,nextBlock,older,workspaceBefore⟩

/-- Actual boundary/heap-floor facts supply every original322 argument and
allocation-frontier premise. The normal return derives the initialized
closed graph, all eight tables and complete empty journal. -/
theorem normal_of_boundary (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rootHash : BitVec 64) (boundary : StateInitBoundary input source)
    (installed : Input.OriginalCode.Installed source.code) (scalars : Input.OriginalScalarGlobals.Scalars source.globals)
    (rootCell : source.locals.lookup (ofString "state_root")=some (.val (.word rootHash)))
    (scratch : Rlp.Validation.Arena source 2713714688#64 2701135872#64)
    (heapFloor : ∃ heap,source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧ 2713731432≤heap.toNat)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ ∃ workspace nodes codes,Output input source post workspace nodes rootHash codes ∧
      source.globals.lookup (ofString "heap_ptr")=some (.val (.word workspace)):=by
  have saved:=boundary
  obtain ⟨array,nodes,codes,heap,nodeData,codeData,nodeCell,codeCell,heapCell,heapArena,aligned,nodeBefore,codeBefore⟩:=boundary
  obtain ⟨floorHeap,floorCell,floorLower⟩:=heapFloor
  have same : heap=floorHeap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (heapCell.symm.trans floorCell)))
  have lower : 2713731432≤heap.toNat:=by rw [same]; exact floorLower
  obtain ⟨zero,output⟩:=body_normal input source post heap nodes rootHash codes saved installed scalars heapCell lower nodeCell rootCell codeCell scratch value normal
  exact ⟨zero,heap,nodes,codes,output,heapCell⟩

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.Output.with_locals
#print axioms InitECandidate.Solver.Mpt.StateInit.normal_of_boundary
