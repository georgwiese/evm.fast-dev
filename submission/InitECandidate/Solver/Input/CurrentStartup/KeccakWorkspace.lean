import InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrame
import InitECandidate.Solver.CurrentKeccak.Environment

namespace InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

private theorem template_state (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (InitializerAllocations.template source cursor keccakActions).globals.lookup (ofString "keccak_st")=
      some (.val (.word (BitVec.ofNat 64 (cursor+192)))) := by
  simp [keccakActions,InitializerAllocations.template,InitializerAllocations.reserve,InitializerAllocations.constant,putGlobal,HolFiniteMapExact.update,FUPDATE,
    show ofString "heap_ptr"≠ofString "keccak_st" from by decide,show ofString "keccak_pad"≠ofString "keccak_st" from by decide]

private theorem template_pad (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (InitializerAllocations.template source cursor keccakActions).globals.lookup (ofString "keccak_pad")=
      some (.val (.word (BitVec.ofNat 64 (cursor+392)))) := by
  simp [keccakActions,InitializerAllocations.template,InitializerAllocations.reserve,InitializerAllocations.constant,putGlobal,HolFiniteMapExact.update,FUPDATE,Nat.add_assoc,
    show ofString "heap_ptr"≠ofString "keccak_pad" from by decide]

/-- Derive the actual state/pad addresses from the same normally completed
first three startup calls. The SSZ initializer preserves both real bindings. -/
theorem first_three_keccak (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString "zero_hashes")=some (.val (.word 0#64)))
    (bounded : cursor≤2952790016) (aligned : cursor%8=0)
    (actual : evaluateHOLFiniteState source (withTail routines .skip)=(none,target)) :
    ∃ sszState,evaluateHOLFiniteState sszState (withTail (routines.drop 3) .skip)=(none,target) ∧
      OriginalCode.Installed sszState.code ∧
      sszState.globals.lookup (ofString "keccak_st")=some (.val (.word (BitVec.ofNat 64 (cursor+384)))) ∧
      sszState.globals.lookup (ofString "keccak_pad")=some (.val (.word (BitVec.ofNat 64 (cursor+584)))) := by
  obtain ⟨shaState,keccakState,sszState,shaRun,keccakRun,sszRun,afterSsz,sszCode,sszScalars,offsets,chunk,zeros,finalHeap,room,sszAligned⟩:=
    first_three source target cursor installed scalars heap zero bounded aligned actual
  obtain ⟨shaBound,shaGlobals⟩:=sha_call source shaState cursor installed scalars heap bounded aligned shaRun
  have shaCode : OriginalCode.Installed shaState.code := by
    rw [(evaluation_fields source shaState _ none shaRun).2.2.2]
    exact installed
  have shaScalars:=written_scalars source shaState cursor shaActions scalars shaGlobals
  have shaHeap : shaState.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 (cursor+192)))) := by
    rw [shaGlobals]
    simpa [shaActions,InitializerAllocations.totalBytes,InitializerAllocations.constant] using InitializerAllocations.template_heap source cursor shaActions heap sha_valid
  obtain ⟨keccakBound,keccakGlobals⟩:=keccak_call shaState keccakState (cursor+192) shaCode shaScalars shaHeap shaBound (by omega) keccakRun
  have keccakCode : OriginalCode.Installed keccakState.code := by
    rw [(evaluation_fields shaState keccakState _ none keccakRun).2.2.2]
    exact shaCode
  have keccakScalars:=written_scalars shaState keccakState (cursor+192) keccakActions shaScalars keccakGlobals
  have keccakHeap : keccakState.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 (cursor+720)))) := by
    rw [keccakGlobals]
    simpa [keccakActions,InitializerAllocations.totalBytes,InitializerAllocations.constant,Nat.add_assoc] using InitializerAllocations.template_heap shaState (cursor+192) keccakActions shaHeap keccak_valid
  have shaZero : shaState.globals.lookup (ofString "zero_hashes")=some (.val (.word 0#64)) :=
    (shaGlobals _).trans ((InitializerAllocations.template_other source cursor shaActions _ (by decide)
      (by intro action member; simp [shaActions] at member; rcases member with rfl|rfl <;> decide)).trans zero)
  have keccakZero : keccakState.globals.lookup (ofString "zero_hashes")=some (.val (.word 0#64)) :=
    (keccakGlobals _).trans ((InitializerAllocations.template_other shaState (cursor+192) keccakActions _ (by decide)
      (by intro action member; simp [keccakActions] at member; rcases member with rfl|rfl|rfl <;> decide)).trans shaZero)
  obtain ⟨sszBound,sszGlobals⟩:=ssz_call keccakState sszState (cursor+720) keccakCode keccakScalars keccakHeap keccakZero (by omega) (by omega) sszRun
  have keep (key : MlS) (different : key≠ofString "heap_ptr")
      (notWritten : ∀ action∈sszActions,key≠ofString action.name) : sszState.globals.lookup key=keccakState.globals.lookup key :=
    (sszGlobals key).trans (InitializerAllocations.template_other keccakState (cursor+720) sszActions key different notWritten)
  have stateCell := (keep (ofString "keccak_st") (by decide)
    (by intro action member; simp [sszActions] at member; rcases member with rfl|rfl|rfl <;> decide)).trans
    ((keccakGlobals _).trans (template_state shaState (cursor+192)))
  have padCell := (keep (ofString "keccak_pad") (by decide)
    (by intro action member; simp [sszActions] at member; rcases member with rfl|rfl|rfl <;> decide)).trans
    ((keccakGlobals _).trans (template_pad shaState (cursor+192)))
  exact ⟨sszState,afterSsz,sszCode,by simpa only [Nat.add_assoc] using stateCell,by simpa only [Nat.add_assoc] using padCell⟩

/-- The actual completed main startup retains state0xa1000180 and
pad0xa1000248 through all later initializers. -/
theorem main_keccak_cells (input : Guest.InputBlob) (origin target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Main.Entry input origin)
    (actual : evaluateHOLFiniteState (Main.memoryState origin) (withTail routines .skip)=(none,target)) :
    target.globals.lookup (ofString "keccak_st")=some (.val (.word 2701132160#64)) ∧
    target.globals.lookup (ofString "keccak_pad")=some (.val (.word 2701132360#64)) := by
  have heap:=(Main.memory_globals origin).1
  rw [entry.base] at heap
  have zero:=(Main.memory_other origin (ofString "zero_hashes") (by decide) (by decide) (by decide)).trans
    (entry.zeros (ofString "zero_hashes") OriginalScalarGlobals.ssz_names.2.2)
  obtain ⟨sszState,suffix,code,stateCell,padCell⟩:=first_three_keccak (Main.memoryState origin) target InitE.sourceBase entry.code (Main.memory_scalars input origin entry) heap zero (by decide) (by decide) actual
  have preserved (workspace : OffsetsFrame.WorkspaceKey) : target.globals.lookup (OffsetsFrame.workspaceKey workspace)=sszState.globals.lookup (OffsetsFrame.workspaceKey workspace) := by
    have frame:=later_prefix sszState.code code (routines.drop 3) (fun routine member=>member) workspace sszState rfl
    rw [suffix] at frame
    exact congrArg Prod.snd frame
  exact ⟨(preserved .keccakState).trans stateCell,(preserved .keccakPad).trans padCell⟩

end InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace

#print axioms InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace.first_three_keccak
#print axioms InitECandidate.Solver.Input.CurrentStartup.EarlyWorkspace.main_keccak_cells

namespace InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrame
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual main decoder and root-allocation prefixes retain both initialized
software-hash pointers, including earlier handler/stopped alternatives. -/
theorem main_keccak_cells {input : Guest.InputBlob}
    {origin source decoded current : PanSemStateFiniteExact 64 Guest.HostMemory}
    (entry : Main.Entry input origin)
    (startup : evaluateHOLFiniteState (Main.memoryState origin) (withTail routines .skip)=(none,source))
    (decoder : CallPrefix.Execution source DecoderPrefix.actions decoded)
    (root : CallPrefix.Execution decoded CurrentHash.RootEntry.actions current) :
    current.globals.lookup (ofString "keccak_st")=some (.val (.word 2701132160#64)) ∧
    current.globals.lookup (ofString "keccak_pad")=some (.val (.word 2701132360#64)) := by
  have sourceCode : OriginalCode.Installed source.code := by
    rw [(evaluation_fields (Main.memoryState origin) source _ none startup).2.2.2]
    exact entry.code
  have decodedCode : OriginalCode.Installed decoded.code := by rw [decoder.runtime.2.2.2.1]; exact sourceCode
  have cells:=EarlyWorkspace.main_keccak_cells input origin source entry startup
  have kept (workspace : WorkspaceKey) : current.globals.lookup (key workspace)=source.globals.lookup (key workspace) :=
    (root.globals (key workspace) (root_prefix workspace decoded.code decodedCode)).trans
      (decoder.globals (key workspace) (decoder_prefix workspace source.code sourceCode))
  exact ⟨(kept .keccakState).trans cells.1,(kept .keccakPad).trans cells.2⟩

end InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrame

#print axioms InitECandidate.Solver.Input.CurrentStartup.WorkspaceFrame.main_keccak_cells
