import InitECandidate.Solver.Input.MainStateInitBoundary
import InitECandidate.Solver.Mpt.StateInitReadyRuntime
import InitECandidate.Solver.Mpt.StateInitReadyHeap
import InitECandidate.Solver.Mpt.StateInitAllocationTrace

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
open WitnessConstructors

/-- Real state_init body execution reaches its actual root materializer
with both constructor-derived databases, current physical heap, original
runtime and initialized workspace. Allocation failures retain their own cost. -/
theorem root_ready_of_entry (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (boundary : StateInitBoundary input source) (installed : OriginalCode.Installed source.code)
    (scalars : OriginalScalarGlobals.Scalars source.globals)
    (rootCell : source.locals.lookup (ofString "state_root")=some (.val (.word root)))
    (scratch : Rlp.Validation.Arena source 2713714688#64 2701135872#64)
    (environment : Keccak256.Environment source 2713714976#64 2713715176#64)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source Mpt.StateInit.body=(outcome,post)) :
    source.clock-post.clock≤2 ∨ ∃ heap nodes codes,
      let current:=Mpt.StateInit.ready source heap nodes root codes
      AllocatedBytes.Arena heap 40 ∧ StateInitBoundary input current ∧ OriginalCode.Installed current.code ∧
      OriginalScalarGlobals.Scalars current.globals ∧ current.locals.lookup (ofString "state_root")=some (.val (.word root)) ∧
      Rlp.Validation.Arena current 2713714688#64 2701135872#64 ∧ Keccak256.Environment current 2713714976#64 2713715176#64 ∧
      current.clock=source.clock-1 ∧ evaluateHOLFiniteState current Mpt.StateInit.rootCall=(outcome,post) := by
  obtain ⟨codeArray,nodes,codes,heap,nodeDatabase,codeDatabase,nodeCell,codeCell,heapCell,heapArena,aligned,nodeBefore,codeBefore⟩ := boundary
  obtain ⟨oldWs,wsCell⟩ := scalars _ Mpt.StateInit.workspace_name
  rcases Mpt.StateInit.allocation_trace source post heap oldWs nodes root codes installed wsCell heapCell nodeCell rootCell codeCell
      nodeDatabase.domain heapArena.lower (by have h:=heapArena.upper; omega) aligned outcome run with stopped|allocated
  · exact Or.inl stopped
  · obtain ⟨funded,arena,continued⟩ := allocated
    let current:=Mpt.StateInit.ready source heap nodes root codes
    have nodeData:=Mpt.StateInit.ready_database source heap nodes root codes _ nodes _ (nodeCount input) 1024 (nodeSlices input) nodeDatabase nodeBefore arena
    have codeData:=Mpt.StateInit.ready_database source heap nodes root codes _ codes _ (codeCount input) 65536 (codeSlices input) codeDatabase codeBefore arena
    have geometry:=Mpt.StateInit.workspace_heap_geometry heap arena aligned
    have grow (table : BitVec 64) (before : MutableTable.WitnessBuild.BeforeHeap current table heap.toNat) :
        MutableTable.WitnessBuild.BeforeHeap current table (PersistentAlloc.rounded heap 40#64).toNat := by
      obtain ⟨capacity,cell,bound⟩ := before
      exact ⟨capacity,cell,bound.trans geometry.2.2⟩
    have fields:=Mpt.StateInit.ready_fields source heap nodes root codes
    have currentNodes : current.locals.lookup (ofString "nodedb")=some (.val (.word nodes)) := by rw [fields.1]; exact nodeCell
    have currentCodes : current.locals.lookup (ofString "codedb")=some (.val (.word codes)) := by rw [fields.1]; exact codeCell
    have currentRoot : current.locals.lookup (ofString "state_root")=some (.val (.word root)) := by rw [fields.1]; exact rootCell
    have currentBoundary : StateInitBoundary input current :=
      ⟨codeArray,nodes,codes,PersistentAlloc.rounded heap 40#64,nodeData.1,codeData.1,currentNodes,currentCodes,fields.2.2.1,
        geometry.1,geometry.2.1,grow nodes nodeData.2,grow codes codeData.2⟩
    exact Or.inr ⟨heap,nodes,codes,arena,currentBoundary,installed,Mpt.StateInit.ready_scalars source heap nodes root codes scalars,currentRoot,
      Mpt.StateInit.ready_scratch source heap nodes root codes _ _ scratch,Mpt.StateInit.ready_environment source heap nodes root codes _ _ environment,rfl,continued⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.root_ready_of_entry
