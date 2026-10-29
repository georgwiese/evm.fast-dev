import InitECandidate.Solver.Input.CurrentHash.RootCut
import InitECandidate.Solver.Input.CurrentStartup.KeccakWorkspace
import InitECandidate.Solver.Input.CurrentStartup.MptReached

namespace InitECandidate.Solver.Input.CurrentHash.WorkspaceEntry
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

abbrev chunkPointer : BitVec 64 := 2701132496#64
abbrev zeroPointer : BitVec 64 := 2701132592#64

/-- Actual initialized hashing workspaces, including the Keccak pointers
needed by the following header-validation phase. Digest bytes are unrestricted. -/
structure Workspace (state : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  code : OriginalCode.Installed state.code
  domain : state.memaddrs = InitE.ordinaryDomain
  little : state.be = false
  offsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word 2701132528#64))
  chunk : state.globals.lookup (ofString "ssz_len_chunk") = some (.val (.word chunkPointer))
  zeros : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroPointer))
  keccakState : state.globals.lookup (ofString "keccak_st") = some (.val (.word 2701132160#64))
  keccakPad : state.globals.lookup (ofString "keccak_pad") = some (.val (.word 2701132360#64))
  mptHash : state.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word 2701134768#64))
  mptKey : state.globals.lookup (ofString "mpt_key_scratch") = some (.val (.word 2701134808#64))
  mptEmpty : state.globals.lookup (ofString "empty_trie_root") = some (.val (.word 2701134640#64))
  shaState : state.globals.lookup (ofString "sha_st") = some (.val (.word 2701131776#64))
  shaPad : state.globals.lookup (ofString "sha_pad") = some (.val (.word 2701131840#64))
  u256 : state.globals.lookup (ofString "u256_ws") = some (.val (.word 2701134824#64))
  chunkArena : AllocatedBytes.Arena chunkPointer 32
  zeroArena : AllocatedBytes.Arena zeroPointer 2048
  chunkAligned : chunkPointer.toNat % 8 = 0
  zeroAligned : zeroPointer.toNat % 8 = 0

/-- These values and extents derive from the actual original initialization,
decoder and root-allocation traces, rather than supplied workspace facts. -/
theorem main {input : Guest.InputBlob}
    {origin source decoded current : PanSemStateFiniteExact 64 Guest.HostMemory}
    (initial : CurrentStartup.HostState input source) (entry : Main.Entry input origin)
    (startup : evaluateHOLFiniteState (Main.memoryState origin) (CurrentStartup.withTail CurrentStartup.routines .skip) = (none, source))
    (decoder : CallPrefix.Execution source CurrentStartup.DecoderPrefix.actions decoded)
    (root : CallPrefix.Execution decoded RootEntry.actions current) : Workspace current := by
  have cells := CurrentStartup.WorkspaceFrame.main_cells entry startup decoder root
  have mpt := CurrentStartup.MptWorkspace.main_decoder_cells entry startup decoder root
  have mptKey := CurrentStartup.MptWorkspace.main_decoder_key_cell entry startup decoder root
  have mptEmpty := CurrentStartup.MptWorkspace.main_decoder_empty_cell entry startup decoder root
  have u256 := CurrentStartup.WorkspaceFrame.main_u256_cell entry startup decoder root
  have sha := CurrentStartup.WorkspaceFrame.main_sha_cells entry startup decoder root
  have keccak := CurrentStartup.WorkspaceFrame.main_keccak_cells entry startup decoder root
  have code : OriginalCode.Installed current.code := by
    rw [root.runtime.2.2.2.1, decoder.runtime.2.2.2.1]
    exact initial.arena.code
  have domain : current.memaddrs = InitE.ordinaryDomain := root.runtime.1.trans (decoder.runtime.1.trans initial.arena.domain)
  have little : current.be = false := root.runtime.2.1.trans (decoder.runtime.2.1.trans initial.little)
  exact ⟨code, domain, little, cells.1, cells.2.1, cells.2.2,keccak.1,keccak.2,mpt,mptKey,mptEmpty,sha.1,sha.2,u256,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, by decide, by decide⟩

theorem Workspace.at_callee {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    (data : Workspace source) (callee : HolFiniteMapExact MlS (ValueHOL 64)) :
    Workspace (callEntryStateHOLFinite source callee) :=
  ⟨data.code, data.domain, data.little, data.offsets, data.chunk, data.zeros,data.keccakState,data.keccakPad,data.mptHash,data.mptKey,data.mptEmpty,data.shaState,data.shaPad,data.u256,
    data.chunkArena, data.zeroArena, data.chunkAligned, data.zeroAligned⟩

theorem Workspace.keccak_environment {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    (data : Workspace source) : CurrentKeccak.Hash.Environment source 2701132160#64 2701132360#64 :=
  ⟨data.code,data.domain,data.keccakState,data.keccakPad,⟨by decide,by decide⟩,⟨by decide,by decide⟩,by decide,by decide⟩

/-- Both concrete workspaces are entirely below the same copied input used
by the actual root-hash caller. -/
theorem input_separation {input : Guest.InputBlob} {decoded current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {origin : CurrentStartup.DecoderOrigin} {record gasWord requestRecord root array : BitVec 64}
    {payloadLength start size : Nat}
    (ready : RootEntry.Ready input decoded current origin record gasWord requestRecord root array payloadLength start size) :
    chunkPointer.toNat + 32 ≤ origin.pointer.toNat ∧ zeroPointer.toNat + 2048 ≤ origin.pointer.toNat := by
  obtain ⟨headerSource, headerReady, headerPost, nodes, codes, headers, nodeStart, nodeLength, codeStart, codeLength,
    headerStart, headerLength, data, frame, clock⟩ := ready.snapshot
  have lower := data.context.pointerLower
  change 2701132496 + 32 ≤ origin.pointer.toNat ∧ 2701132592 + 2048 ≤ origin.pointer.toNat
  omega

/-- Refinement reuses the same execution split, including all earlier stops. -/
theorem refine {input : Guest.InputBlob} {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {result : Option (PanSemResultExact 64)} (initial : CurrentStartup.HostState input source)
    (entry : Main.Entry input origin)
    (startup : evaluateHOLFiniteState (Main.memoryState origin) (CurrentStartup.withTail CurrentStartup.routines .skip) = (none, source))
    (cut : RootCut.ThroughDecoder input source result post) : RootCut.ThroughDecoder input source result post Workspace :=
  cut.with_ready Workspace (fun decoded current decoder root => main initial entry startup decoder root)

/-- Whole-source observations now supply the actual current software hash
workspace at the reached root caller, preserving original outcomes and events. -/
theorem reached (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (terminates : InitE.sourceBehaviour input = .terminate outcome events)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) :
    ∃ origin target result actualOutcome,
      Main.Entry input origin ∧
      ((∃ middle, evaluateHOLFiniteState (Main.memoryState origin) (CurrentStartup.withTail CurrentStartup.routines .skip) = (none, middle) ∧
          CurrentStartup.HostState input middle ∧ RootCut.ThroughDecoder input middle result target Workspace) ∨
        (∃ stopped, evaluateHOLFiniteState (Main.memoryState origin) (CurrentStartup.withTail CurrentStartup.routines .skip) = (some stopped, target) ∧
          result = some stopped ∧ CurrentStartup.ArenaState target)) ∧
      (match result with
       | some (.finalFfi event) => actualOutcome = HolOutcome.ffiOutcome event
       | some (.returned _) => actualOutcome = HolOutcome.success
       | _ => False) ∧
      HolBehaviour.terminate outcome events = .terminate actualOutcome target.ffi.ioEvents := by
  obtain ⟨origin, target, result, actualOutcome, entry, startup, classified, observation⟩ :=
    RootCut.reached input outcome events terminates gas
  refine ⟨origin, target, result, actualOutcome, entry, ?_, classified, observation⟩
  rcases startup with continued | stopped
  · obtain ⟨middle, startupRun, initial, actual⟩ := continued
    exact Or.inl ⟨middle, startupRun, initial, refine initial entry startupRun actual⟩
  · exact Or.inr stopped

end InitECandidate.Solver.Input.CurrentHash.WorkspaceEntry

#print axioms InitECandidate.Solver.Input.CurrentHash.WorkspaceEntry.main
#print axioms InitECandidate.Solver.Input.CurrentHash.WorkspaceEntry.Workspace.at_callee
#print axioms InitECandidate.Solver.Input.CurrentHash.WorkspaceEntry.input_separation
#print axioms InitECandidate.Solver.Input.CurrentHash.WorkspaceEntry.refine
#print axioms InitECandidate.Solver.Input.CurrentHash.WorkspaceEntry.reached

#print axioms InitECandidate.Solver.Input.CurrentHash.WorkspaceEntry.Workspace.keccak_environment
