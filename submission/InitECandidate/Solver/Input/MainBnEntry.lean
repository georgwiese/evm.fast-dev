import InitECandidate.Solver.Input.MainSecpPrefix
import InitECandidate.Solver.Input.MainBnProgram

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def initializedNames : List String := ["heap_ptr","scratch_ptr","frame_mem_ptr","sha_st","sha_pad","sha_accel","keccak_st","keccak_pad",
  "ssz_len_chunk","ssz_offs","zero_hashes","empty_trie_root","empty_code_hash","mpt_nib_scratch","mpt_hash_scratch","mpt_key_scratch","u256_ws","secp_accel_scratch"]

/-- A declaration-zero scalar outside the preceding startup writes is still
zero at the actual reached secp continuation. -/
theorem secp_initial_zero (input : Guest.InputBlob) (source middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (reached : MptReached source middle) (key : MlS) (member : key ∈ OriginalScalarGlobals.names)
    (untouched : ∀ name ∈ initializedNames,key ≠ ofString name) :
    (secpState middle).globals.lookup key = some (.val (.word 0#64)) := by
  have heap := untouched "heap_ptr" (by simp [initializedNames])
  have secp := SecpInitialization.template_other (u256State middle) 2713718280 key heap (untouched "secp_accel_scratch" (by simp [initializedNames]))
  change (SecpInitialization.template (u256State middle) 2713718280).globals.lookup key = _
  rw [secp]
  have workspace : (u256State middle).globals.lookup key = middle.globals.lookup key := by
    apply InitializerAllocations.template_other middle 2713717640 U256Initialization.actions key heap
    intro action found
    simp only [U256Initialization.actions,List.mem_cons,List.not_mem_nil,or_false] at found
    subst action
    exact untouched "u256_ws" (by simp [initializedNames])
  rw [workspace]
  have globals := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals) reached.control
  change middle.globals = (MptInitialization.allocated (sszState source) 2713717456).globals at globals
  rw [globals]
  have mpt := MptInitialization.allocated_other (sszState source) 2713717456 key heap
    (untouched "empty_trie_root" (by simp [initializedNames])) (untouched "empty_code_hash" (by simp [initializedNames]))
    (untouched "mpt_nib_scratch" (by simp [initializedNames])) (untouched "mpt_hash_scratch" (by simp [initializedNames])) (untouched "mpt_key_scratch" (by simp [initializedNames]))
  have ssz := SszInitialization.template_other (keccakState source) 2713715312 key heap
    (untouched "ssz_len_chunk" (by simp [initializedNames])) (untouched "ssz_offs" (by simp [initializedNames])) (untouched "zero_hashes" (by simp [initializedNames]))
  have keccak := KeccakInitialization.template_other (shaState source) 2713714976 key heap
    (untouched "keccak_st" (by simp [initializedNames])) (untouched "keccak_pad" (by simp [initializedNames]))
  have sha := ShaInitialization.template_other (memoryState source) 2713714688 key heap
    (untouched "sha_st" (by simp [initializedNames])) (untouched "sha_pad" (by simp [initializedNames])) (untouched "sha_accel" (by simp [initializedNames]))
  have memory := memory_other source key heap (untouched "scratch_ptr" (by simp [initializedNames])) (untouched "frame_mem_ptr" (by simp [initializedNames]))
  exact mpt.trans (ssz.trans (keccak.trans (sha.trans (memory.trans (entry.zeros key member)))))

theorem bn_gamma_before (input : Guest.InputBlob) (source middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (reached : MptReached source middle) :
    (secpState middle).globals.lookup (ofString "bn_gamma") = some (.val (.word 0#64)) := by
  apply secp_initial_zero input source middle entry reached _ BnInitialization.symbol_members.1
  intro name member
  simp only [initializedNames,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem bn_params_before (input : Guest.InputBlob) (source middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (reached : MptReached source middle) :
    (secpState middle).globals.lookup (ofString "bn_accel_params") = some (.val (.word 0#64)) := by
  apply secp_initial_zero input source middle entry reached _ (BnAccelInitialization.symbol_member "bn_accel_params" (by simp [BnAccelInitialization.symbols]))
  intro name member
  simp only [initializedNames,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem oracle_of_hash (source : PanSemStateFiniteExact 64 Guest.HostMemory) : (KeccakAbsorb.hashControl source).ffi.oracle = source.ffi.oracle := rfl
private theorem endian_of_hash (source : PanSemStateFiniteExact 64 Guest.HostMemory) : (KeccakAbsorb.hashControl source).be = source.be := rfl
private theorem endian_of_context (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (same : InitializerAllocations.context target = InitializerAllocations.context source) : target.be = source.be := congrArg (fun state => state.be) same

theorem secp_oracle (input : Guest.InputBlob) (source middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (reached : MptReached source middle) : (secpState middle).ffi.oracle = InitE.sourceOracle := by
  have actual : middle.ffi.oracle = (MptInitialization.allocated (sszState source) 2713717456).ffi.oracle :=
    (oracle_of_hash middle).symm.trans ((congrArg (fun state => state.ffi.oracle) reached.control).trans (oracle_of_hash _))
  have allocated := InitializerAllocations.oracle_of_context (sszState source) (MptInitialization.allocated (sszState source) 2713717456)
    (InitializerAllocations.template_context (sszState source) 2713717456 MptInitialization.actions)
  have ssz := InitializerAllocations.oracle_of_context source (sszState source) (ssz_context source)
  exact (InitializerAllocations.oracle_of_context middle (secpState middle) (secp_context middle)).trans
    (actual.trans (allocated.trans (ssz.trans entry.oracle)))

theorem secp_little (input : Guest.InputBlob) (source middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (reached : MptReached source middle) : (secpState middle).be = false := by
  have actual : middle.be = (MptInitialization.allocated (sszState source) 2713717456).be :=
    (endian_of_hash middle).symm.trans ((congrArg (fun state => state.be) reached.control).trans (endian_of_hash _))
  have allocated := endian_of_context (sszState source) (MptInitialization.allocated (sszState source) 2713717456)
    (InitializerAllocations.template_context (sszState source) 2713717456 MptInitialization.actions)
  have ssz := endian_of_context source (sszState source) (ssz_context source)
  exact (endian_of_context middle (secpState middle) (secp_context middle)).trans (actual.trans (allocated.trans (ssz.trans entry.little)))

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.secp_initial_zero
#print axioms InitECandidate.Solver.Input.Main.bn_gamma_before
#print axioms InitECandidate.Solver.Input.Main.bn_params_before
#print axioms InitECandidate.Solver.Input.Main.secp_oracle
#print axioms InitECandidate.Solver.Input.Main.secp_little
