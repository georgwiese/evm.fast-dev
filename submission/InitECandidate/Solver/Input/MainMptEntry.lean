import InitECandidate.Solver.Input.MainSszPrefix
import InitECandidate.Solver.WitnessRadix.KeccakOriginalEnvironment
import InitECandidate.Solver.Input.InitializerControl

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

theorem KeccakInitialization.template_bindings (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (KeccakInitialization.template source cursor).globals.lookup (ofString "keccak_st") = some (.val (.word (BitVec.ofNat 64 cursor))) ∧
    (KeccakInitialization.template source cursor).globals.lookup (ofString "keccak_pad") = some (.val (.word (BitVec.ofNat 64 (cursor + 200)))) := by
  simp [KeccakInitialization.template,KeccakInitialization.actions,InitializerAllocations.template,InitializerAllocations.reserve,
    InitializerAllocations.constant,putGlobal,HolFiniteMapExact.update,FUPDATE,
    show ofString "keccak_pad" ≠ ofString "keccak_st" by decide,
    show ofString "heap_ptr" ≠ ofString "keccak_st" by decide]

theorem ssz_scalars (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (entry : Entry input source) :
    OriginalScalarGlobals.Scalars (sszState source).globals :=
  SszInitialization.template_scalars (keccakState source) 2713715312
    (KeccakInitialization.template_scalars (shaState source) 2713714976
      (ShaInitialization.template_scalars (memoryState source) 2713714688 (memory_scalars input source entry)))

theorem ssz_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    (sszState source).globals.lookup (ofString "heap_ptr") = some (.val (.word 2713717456#64)) :=
  SszInitialization.template_heap (keccakState source) 2713715312
    (KeccakInitialization.template_heap (shaState source) 2713714976
      (ShaInitialization.template_heap (memoryState source) 2713714688))

theorem SszInitialization.template_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    InitializerAllocations.context (SszInitialization.template source cursor) = InitializerAllocations.context source := by
  unfold SszInitialization.template InitializerWords.written
  rw [InitializerAllocations.context_memory]
  exact InitializerAllocations.template_context source cursor SszInitialization.actions

theorem ssz_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    InitializerAllocations.context (sszState source) = InitializerAllocations.context source := by
  have memory : InitializerAllocations.context (memoryState source) = InitializerAllocations.context source := rfl
  have sha : InitializerAllocations.context (shaState source) = InitializerAllocations.context (memoryState source) := rfl
  have keccak : InitializerAllocations.context (keccakState source) = InitializerAllocations.context (shaState source) := by
    unfold keccakState
    rw [InitializerAllocations.context_clock]
    exact InitializerAllocations.template_context (shaState source) 2713714976 KeccakInitialization.actions
  have ssz : InitializerAllocations.context (sszState source) = InitializerAllocations.context (keccakState source) := by
    unfold sszState
    rw [InitializerAllocations.context_clock,SszInitialization.template_context]
  exact ssz.trans (keccak.trans (sha.trans memory))

theorem ssz_code (source : PanSemStateFiniteExact 64 Guest.HostMemory) : (sszState source).code = source.code :=
  (InitializerAllocations.context_code (sszState source)).symm.trans
    ((congrArg (fun s => s.code) (ssz_context source)).trans (InitializerAllocations.context_code source))

/-- Both hash workspaces and their actual code/oracle are supplied by the
preceding main initialization; no future helper environment is assumed. -/
theorem ssz_hash_environment (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (entry : Entry input source) :
    Keccak256.Environment (sszState source) 2713714976#64 2713715176#64 := by
  obtain ⟨state,pad⟩ := KeccakInitialization.template_bindings (shaState source) 2713714976
  have installed : OriginalCode.Installed (sszState source).code := by rw [ssz_code]; exact entry.code
  have domain : (sszState source).memaddrs = InitE.ordinaryDomain :=
    ((InitializerAllocations.context_domain (sszState source)).symm.trans
      ((congrArg (fun s => s.memaddrs) (ssz_context source)).trans (InitializerAllocations.context_domain source))).trans entry.domain
  have oracle : (sszState source).ffi.oracle = InitE.sourceOracle :=
    ((InitializerAllocations.context_oracle (sszState source)).symm.trans
      ((congrArg (fun s => s.ffi.oracle) (ssz_context source)).trans (InitializerAllocations.context_oracle source))).trans entry.oracle
  apply Keccak256.original_environment (sszState source) 2713714976#64 2713715176#64 installed domain oracle
  · exact (SszInitialization.template_other (keccakState source) 2713715312 (ofString "keccak_st") (by decide) (by decide) (by decide) (by decide)).trans state
  · exact (SszInitialization.template_other (keccakState source) 2713715312 (ofString "keccak_pad") (by decide) (by decide) (by decide) (by decide)).trans pad

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.KeccakInitialization.template_bindings
#print axioms InitECandidate.Solver.Input.Main.ssz_scalars
#print axioms InitECandidate.Solver.Input.Main.ssz_heap
#print axioms InitECandidate.Solver.Input.Main.ssz_code
#print axioms InitECandidate.Solver.Input.Main.ssz_context
#print axioms InitECandidate.Solver.Input.Main.SszInitialization.template_context
#print axioms InitECandidate.Solver.Input.Main.ssz_hash_environment
