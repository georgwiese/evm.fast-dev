import InitECandidate.Solver.CurrentKeccak.Memory

namespace InitECandidate.Solver.CurrentKeccak.Hash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

theorem call_globals (key : MlS) (code) (installed : OriginalCode.Installed code) (arguments : List (ExpHOL 64)) :
    GlobalEffects.Preserves key code (.call (some (none,none)) (ofString "keccak256") arguments) :=
  GlobalEffects.call_body key code (some none) _ arguments formals body .one (original_code code installed) (hash_globals key code installed)

/-- Genuine whole-hash callers retain their workspace, caller locals and
any word outside the actual state/pad/output buffers. The frame covers the
current software body and derives every normal inner phase from this call. -/
theorem call_span_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad pointer out query : BitVec 64) (length : Nat)
    (environment : Environment source stp pad) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values pointer out length))
    (small : length+136<2^64) (outArena : AllocatedBytes.Arena out 32)
    (stateAway : CopyGeneral.Away stp query 200) (padAway : CopyGeneral.Away pad query 136) (outAway : CopyGeneral.Away out query 32)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "keccak256") arguments)=(none,post)) : Frame source post stp pad query := by
  obtain ⟨callee,called,pointerCell,countCell,outCell⟩:=Hash.environment source.code.lookup pointer out length (original_code source.code environment.installed)
  have ready : Environment (callEntryStateHOLFinite source callee) stp pad := environment.of_frame rfl
  have memory : post.memory query=source.memory query := by
    apply MemoryAt.call_normal source post _ arguments (values pointer out length) body callee .one query args called ?_ run
    intro target value bodyRun
    exact body_memory (callEntryStateHOLFinite source callee) target stp pad pointer out query length ready pointerCell countCell outCell small outArena stateAway padAway outAway value bodyRun
  exact ⟨environment.after _ _ (fun key=>call_globals key source.code environment.installed arguments) run,memory,
    fun key=>CallNormal.ignored_lookup source post key (ofString "keccak256") arguments run⟩

/-- Genuine whole-hash callers retain their workspace, caller locals and
any word outside the actual state/pad/output buffers. The frame covers the
current software body and derives every normal inner phase from this call. -/
theorem call_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad pointer out query : BitVec 64) (length : Nat)
    (environment : Environment source stp pad) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values pointer out length))
    (inputArena : AllocatedBytes.Arena pointer length) (outArena : AllocatedBytes.Arena out 32)
    (stateAway : CopyGeneral.Away stp query 200) (padAway : CopyGeneral.Away pad query 136) (outAway : CopyGeneral.Away out query 32)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "keccak256") arguments)=(none,post)) : Frame source post stp pad query := by
  have small : length+136<2^64:=by have upper:=inputArena.upper; omega
  exact call_span_frame source post stp pad pointer out query length environment arguments args small outArena stateAway padAway outAway run

end InitECandidate.Solver.CurrentKeccak.Hash

#print axioms InitECandidate.Solver.CurrentKeccak.Hash.call_globals
#print axioms InitECandidate.Solver.CurrentKeccak.Hash.call_frame

#print axioms InitECandidate.Solver.CurrentKeccak.Hash.call_span_frame

namespace InitECandidate.Solver.CurrentKeccak
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem permutation_metadata (code) : MemoryMetadata.Preserves code Permutation.body := by
  simp only [Permutation.body,Guest.Software.guestFn_keccak_f1600,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  repeat first
    | exact MemoryMetadata.skip code
    | apply MemoryMetadata.declared
    | apply MemoryMetadata.sequence
    | apply MemoryMetadata.loop
    | exact MemoryMetadata.assign code _ _
    | exact MemoryMetadata.store code _ _
    | exact MemoryMetadata.returned code _

theorem absorb_metadata (code) (installed : OriginalCode.Installed code) : MemoryMetadata.Preserves code Absorb.body := by
  rw [Absorb.body_shape]
  apply MemoryMetadata.declared
  apply MemoryMetadata.sequence
  · apply MemoryMetadata.conditional
    all_goals
      apply MemoryMetadata.loop
      apply MemoryMetadata.sequence
      · exact MemoryMetadata.store code _ _
      · exact MemoryMetadata.assign code _ _
  · apply MemoryMetadata.sequence
    · exact MemoryMetadata.call_body code (some none) _ _ Permutation.formals Permutation.body .one
        (Permutation.original_code code installed) (permutation_metadata code)
    · exact MemoryMetadata.returned code _

theorem zero_metadata (code) : MemoryMetadata.Preserves code Zero.body := by
  simp only [Zero.body,Guest.Software.guestFn_memzero,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  repeat first
    | exact MemoryMetadata.skip code
    | apply MemoryMetadata.declared
    | apply MemoryMetadata.sequence
    | apply MemoryMetadata.conditional
    | apply MemoryMetadata.loop
    | exact MemoryMetadata.assign code _ _
    | exact MemoryMetadata.store code _ _
    | exact MemoryMetadata.byte_store code _ _
    | exact MemoryMetadata.returned code _

theorem copy_metadata (code) : MemoryMetadata.Preserves code Copy32.body := by
  simp only [Copy32.body,Guest.Software.guestFn_memcpy,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  repeat first
    | exact MemoryMetadata.skip code
    | apply MemoryMetadata.declared
    | apply MemoryMetadata.sequence
    | apply MemoryMetadata.conditional
    | apply MemoryMetadata.loop
    | exact MemoryMetadata.assign code _ _
    | exact MemoryMetadata.store code _ _
    | exact MemoryMetadata.byte_store code _ _
    | exact MemoryMetadata.returned code _

/-- The whole fixed software hash retains all nonmemory runtime fields,
including every global and FFI field, on every outcome and at every clock. -/
theorem hash_metadata (code) (installed : OriginalCode.Installed code) : MemoryMetadata.Preserves code Hash.body := by
  simp only [Hash.body,Guest.Software.guestFn_keccak256,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  repeat first
    | exact MemoryMetadata.skip code
    | apply MemoryMetadata.declared
    | apply MemoryMetadata.sequence
    | apply MemoryMetadata.conditional
    | apply MemoryMetadata.loop
    | exact MemoryMetadata.assign code _ _
    | exact MemoryMetadata.store code _ _
    | exact MemoryMetadata.byte_store code _ _
    | exact MemoryMetadata.returned code _
    | exact MemoryMetadata.call_body code (some none) (ofString "memzero") _ Zero.formals Zero.body .one
        (Zero.original_code code installed) (zero_metadata code)
    | exact MemoryMetadata.call_body code (some none) (ofString "memcpy") _ CopyGeneral.formals Copy32.body .one
        (CopyGeneral.original_code code installed) (copy_metadata code)
    | exact MemoryMetadata.call_body code (some none) (ofString "keccak_absorb_block") _ Absorb.formals Absorb.body .one
        (Absorb.original_code code installed) (absorb_metadata code installed)

theorem Hash.call_metadata (code) (installed : OriginalCode.Installed code) (arguments : List (ExpHOL 64))
    (destination : Option (Option MlS)) :
    MemoryMetadata.Preserves code (.call (LocalEffects.callInfo destination) (ofString "keccak256") arguments) :=
  MemoryMetadata.call_body code destination (ofString "keccak256") arguments Hash.formals Hash.body .one
    (Hash.original_code code installed) (hash_metadata code installed)

end InitECandidate.Solver.CurrentKeccak

#print axioms InitECandidate.Solver.CurrentKeccak.permutation_metadata
#print axioms InitECandidate.Solver.CurrentKeccak.absorb_metadata
#print axioms InitECandidate.Solver.CurrentKeccak.zero_metadata
#print axioms InitECandidate.Solver.CurrentKeccak.copy_metadata
#print axioms InitECandidate.Solver.CurrentKeccak.hash_metadata
#print axioms InitECandidate.Solver.CurrentKeccak.Hash.call_metadata
