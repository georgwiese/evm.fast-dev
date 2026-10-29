import InitECandidate.Solver.Input.CurrentStartup.MptWorkspace
import InitECandidate.Solver.Input.CurrentStartup.StartupHeap

namespace InitECandidate.Solver.Input.CurrentStartup.MptWorkspace
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem template_empty (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (InitializerAllocations.template source cursor actions).globals.lookup (ofString "empty_trie_root")=
      some (.val (.word (BitVec.ofNat 64 cursor))) := by
  simp [actions,InitializerAllocations.template,InitializerAllocations.reserve,InitializerAllocations.constant,
    putGlobal,HolFiniteMapExact.update,FUPDATE,Nat.add_assoc,
    show ofString "heap_ptr"≠ofString "empty_trie_root" from by decide,
    show ofString "empty_code_hash"≠ofString "empty_trie_root" from by decide,
    show ofString "mpt_nib_scratch"≠ofString "empty_trie_root" from by decide,
    show ofString "mpt_hash_scratch"≠ofString "empty_trie_root" from by decide,
    show ofString "mpt_key_scratch"≠ofString "empty_trie_root" from by decide]

theorem template_hash (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (InitializerAllocations.template source cursor actions).globals.lookup (ofString "mpt_hash_scratch") =
      some (.val (.word (BitVec.ofNat 64 (cursor+128)))) := by
  simp [actions,InitializerAllocations.template,InitializerAllocations.reserve,InitializerAllocations.constant,
    putGlobal,HolFiniteMapExact.update,FUPDATE,Nat.add_assoc,
    show ofString "heap_ptr" ≠ ofString "mpt_hash_scratch" from by decide,
    show ofString "mpt_key_scratch" ≠ ofString "mpt_hash_scratch" from by decide]

theorem template_key (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (InitializerAllocations.template source cursor actions).globals.lookup (ofString "mpt_key_scratch") =
      some (.val (.word (BitVec.ofNat 64 (cursor+168)))) := by
  simp [actions,InitializerAllocations.template,InitializerAllocations.reserve,InitializerAllocations.constant,
    putGlobal,HolFiniteMapExact.update,FUPDATE,Nat.add_assoc,
    show ofString "heap_ptr" ≠ ofString "mpt_key_scratch" from by decide]

/-- The fourth actual initializer establishes the real hash buffer and the
heap beyond it. All successful allocations are extracted from this same run. -/
theorem first_four (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString "zero_hashes") = some (.val (.word 0#64)))
    (bounded : cursor ≤ 2952790016) (aligned : cursor%8=0)
    (actual : evaluateHOLFiniteState source (withTail routines .skip) = (none,target)) :
    ∃ mptState, evaluateHOLFiniteState mptState (withTail (routines.drop 4) .skip) = (none,target) ∧
      OriginalCode.Installed mptState.code ∧ OriginalScalarGlobals.Scalars mptState.globals ∧
      mptState.globals.lookup (ofString "empty_trie_root")=some (.val (.word (BitVec.ofNat 64 (cursor+2864)))) ∧
      mptState.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word (BitVec.ofNat 64 (cursor+2992)))) ∧
      mptState.globals.lookup (ofString "mpt_key_scratch") = some (.val (.word (BitVec.ofNat 64 (cursor+3032)))) ∧
      mptState.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor+3048)))) ∧
      cursor+3048 ≤ 2952790016 ∧ (cursor+3048)%8=0 := by
  obtain ⟨shaState,keccakState,sszState,shaRun,keccakRun,sszRun,afterSsz,sszCode,sszScalars,offsets,chunk,zeros,sszHeap,room,sszAligned⟩ :=
    EarlyWorkspace.first_three source target cursor installed scalars heap zero bounded aligned actual
  change evaluateHOLFiniteState sszState (.seq (.call (some (none,none)) (Code.name .mpt_init) [])
    (withTail (routines.drop 4) .skip)) = (none,target) at afterSsz
  obtain ⟨mptState,mptRun,afterMpt⟩ := sequence_none sszState target _ _ afterSsz
  obtain ⟨mptRoom,globals⟩ := caller sszState mptState (cursor+2864) sszCode sszScalars sszHeap room sszAligned mptRun
  have mptCode : OriginalCode.Installed mptState.code := by
    rw [(evaluation_fields sszState mptState _ none mptRun).2.2.2]
    exact sszCode
  have hashCell := (globals _).trans (template_hash sszState (cursor+2864))
  have emptyCell := (globals _).trans (template_empty sszState (cursor+2864))
  have keyCell := (globals _).trans (template_key sszState (cursor+2864))
  have mptHeap := (globals _).trans (InitializerAllocations.template_heap sszState (cursor+2864) actions sszHeap valid)
  refine ⟨mptState,afterMpt,mptCode,EarlyWorkspace.written_scalars sszState mptState (cursor+2864) actions sszScalars globals,emptyCell,?_,?_,?_,by omega,by omega⟩
  · simpa only [Nat.add_assoc] using hashCell
  · simpa only [Nat.add_assoc] using keyCell
  · simpa [actions,InitializerAllocations.totalBytes,InitializerAllocations.constant,Nat.add_assoc] using mptHeap

theorem later_body (code) (installed : OriginalCode.Installed code) (routine : Code.Routine)
    (member : routine ∈ routines.drop 4) (workspace : WorkspaceFrameCore.WorkspaceKey := .mptHash) :
    GlobalEffects.Preserves (WorkspaceFrameCore.workspaceKey workspace) code (Code.body routine) := by
  change routine ∈ [.u256_ws_init,.secp256k1_init,.bn254_init,.bls_precompiles_init,
    .ripemd160_init,.blake2_init,.header_init,.evm_init,.fork_init] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact WorkspaceFrameCore.u256_ws_init code installed workspace
  · exact WorkspaceFrameCore.secp256k1_init code installed workspace
  · exact WorkspaceFrameCore.bn254_init code installed workspace
  · exact WorkspaceFrameCore.bls_precompiles_init code installed workspace
  · exact WorkspaceFrameCore.ripemd160_init code installed workspace
  · exact WorkspaceFrameCore.blake2_init code installed workspace
  · exact WorkspaceFrameCore.header_init code installed workspace
  · exact WorkspaceFrameCore.evm_init code installed workspace
  · exact WorkspaceFrameCore.fork_init code installed workspace

theorem later_prefix (code) (installed : OriginalCode.Installed code) (functions : List Code.Routine)
    (inside : ∀ routine ∈ functions, routine ∈ routines.drop 4) (workspace : WorkspaceFrameCore.WorkspaceKey := .mptHash) :
    GlobalEffects.Preserves (WorkspaceFrameCore.workspaceKey workspace) code (withTail functions .skip) := by
  induction functions with
  | nil => exact GlobalEffects.skip _ code
  | cons routine rest ih =>
    apply GlobalEffects.sequence _ code _ _
    · exact GlobalEffects.call_body _ code (some none) (Code.name routine) []
        (Code.formals routine) (Code.body routine) (Code.shape routine)
        (Code.installed code installed routine) (later_body code installed routine (inside routine (by simp)) workspace)
    · exact ih (fun child member => inside child (by simp [member]))

/-- Main's actual startup puts the 40-byte MPT hash buffer strictly before
all subsequent persistent input allocations, including the real EVM release. -/
theorem main_cells (input : Guest.InputBlob) (origin target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Main.Entry input origin)
    (actual : evaluateHOLFiniteState (Main.memoryState origin) (withTail routines .skip) = (none,target)) :
    target.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word 2701134768#64)) ∧
    NormalHeapEffects.AtLeast 2701134824 target := by
  have heap := (Main.memory_globals origin).1
  rw [entry.base] at heap
  have zero := (Main.memory_other origin (ofString "zero_hashes") (by decide) (by decide) (by decide)).trans
    (entry.zeros (ofString "zero_hashes") OriginalScalarGlobals.ssz_names.2.2)
  obtain ⟨mptState,suffix,code,scalars,emptyCell,hashCell,keyCell,heapCell,room,aligned⟩ :=
    first_four (Main.memoryState origin) target InitE.sourceBase entry.code (Main.memory_scalars input origin entry)
      heap zero (by decide) (by decide) actual
  have frame := later_prefix mptState.code code (routines.drop 4) (fun routine member => member) .mptHash mptState rfl
  rw [suffix] at frame
  have same := congrArg Prod.snd frame
  have initial : NormalHeapEffects.AtLeast 2701134824 mptState :=
    ⟨2701134824#64,heapCell,by decide,by decide,by decide⟩
  have pure := StartupHeap.sequence mptState.code code (routines.drop 4) (fun routine member => List.mem_of_mem_drop member)
  have reached := pure mptState rfl 2701134824 initial (by rw [suffix]; trivial)
  rw [suffix] at reached
  exact ⟨same.trans hashCell,reached⟩


/-- Main's same actual startup also establishes the adjacent16-byte
indexed-key scratch allocation; later initializers preserve its global. -/
theorem main_key_cell (input : Guest.InputBlob) (origin target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Main.Entry input origin)
    (actual : evaluateHOLFiniteState (Main.memoryState origin) (withTail routines .skip) = (none,target)) :
    target.globals.lookup (ofString "mpt_key_scratch")=some (.val (.word 2701134808#64)) := by
  have heap := (Main.memory_globals origin).1
  rw [entry.base] at heap
  have zero := (Main.memory_other origin (ofString "zero_hashes") (by decide) (by decide) (by decide)).trans
    (entry.zeros (ofString "zero_hashes") OriginalScalarGlobals.ssz_names.2.2)
  obtain ⟨mptState,suffix,code,scalars,emptyCell,hashCell,keyCell,heapCell,room,aligned⟩ :=
    first_four (Main.memoryState origin) target InitE.sourceBase entry.code (Main.memory_scalars input origin entry)
      heap zero (by decide) (by decide) actual
  have frame := later_prefix mptState.code code (routines.drop 4) (fun routine member => member) .mptKey mptState rfl
  rw [suffix] at frame
  exact (congrArg Prod.snd frame).trans keyCell

theorem main_empty_cell (input : Guest.InputBlob) (origin target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Main.Entry input origin)
    (actual : evaluateHOLFiniteState (Main.memoryState origin) (withTail routines .skip)=(none,target)) :
    target.globals.lookup (ofString "empty_trie_root")=some (.val (.word 2701134640#64)) := by
  have heap:=(Main.memory_globals origin).1
  rw [entry.base] at heap
  have zero:=(Main.memory_other origin (ofString "zero_hashes") (by decide) (by decide) (by decide)).trans
    (entry.zeros (ofString "zero_hashes") OriginalScalarGlobals.ssz_names.2.2)
  obtain ⟨mptState,suffix,code,scalars,emptyCell,hashCell,keyCell,heapCell,room,aligned⟩:=
    first_four (Main.memoryState origin) target InitE.sourceBase entry.code (Main.memory_scalars input origin entry)
      heap zero (by decide) (by decide) actual
  have frame:=later_prefix mptState.code code (routines.drop 4) (fun routine member=>member) .mptEmpty mptState rfl
  rw [suffix] at frame
  exact (congrArg Prod.snd frame).trans emptyCell


end InitECandidate.Solver.Input.CurrentStartup.MptWorkspace

#print axioms InitECandidate.Solver.Input.CurrentStartup.MptWorkspace.first_four
#print axioms InitECandidate.Solver.Input.CurrentStartup.MptWorkspace.main_cells

#print axioms InitECandidate.Solver.Input.CurrentStartup.MptWorkspace.template_key
#print axioms InitECandidate.Solver.Input.CurrentStartup.MptWorkspace.main_key_cell
#print axioms InitECandidate.Solver.Input.CurrentStartup.MptWorkspace.template_empty
#print axioms InitECandidate.Solver.Input.CurrentStartup.MptWorkspace.main_empty_cell
