import InitECandidate.Solver.Input.MainHeaderPrefix

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def postSszNames : List String :=
  ["heap_ptr","empty_trie_root","empty_code_hash","mpt_nib_scratch","mpt_hash_scratch","mpt_key_scratch","u256_ws","secp_accel_scratch","bn_gamma","bn_b2","bn_expw"] ++
  BnAccelInitialization.symbols ++ ["bls_c","bls_discount"] ++ BlsFpInitialization.symbols ++ BlsPairInitialization.symbols ++
  RipemdInitialization.symbols ++ BlakeInitialization.symbols ++ ["hdr_zero8"]

open scoped InitE.MetadataComputation InitE.NameComputation in
theorem keccak_globals_preserved_check : ["keccak_st","keccak_pad"].all (fun key => postSszNames.all (fun name => decide (ofString key ≠ ofString name))) = true := by decide_cbv

private theorem globals_of_hash (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (same : KeccakAbsorb.hashControl target = KeccakAbsorb.hashControl source) : target.globals = source.globals := congrArg (fun state => state.globals) same

private theorem oracle_of_hash (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (same : KeccakAbsorb.hashControl target = KeccakAbsorb.hashControl source) : target.ffi.oracle = source.ffi.oracle := congrArg (fun state => state.ffi.oracle) same

/-- All real global writes since the SSZ boundary are accounted for, so
the Keccak workspace bindings reach EVM initialization unchanged. -/
theorem header_from_ssz (source mptMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (mpt : MptReached source mptMiddle) (reached : BnReached source mptMiddle middle)
    (key : MlS) (different : ∀ name ∈ postSszNames,key ≠ ofString name) :
    (headerState middle).globals.lookup key = (sszState source).globals.lookup key := by
  have heap := different "heap_ptr" (by simp [postSszNames])
  have mptOther := MptInitialization.allocated_other (sszState source) 2713717456 key heap
    (different "empty_trie_root" (by simp [postSszNames])) (different "empty_code_hash" (by simp [postSszNames]))
    (different "mpt_nib_scratch" (by simp [postSszNames])) (different "mpt_hash_scratch" (by simp [postSszNames])) (different "mpt_key_scratch" (by simp [postSszNames]))
  have u256Other : (u256State mptMiddle).globals.lookup key = mptMiddle.globals.lookup key :=
    InitializerAllocations.template_other mptMiddle 2713717640 U256Initialization.actions key heap
      (by intro action member; simp only [U256Initialization.actions,List.mem_cons,List.not_mem_nil,or_false] at member; subst action; exact different "u256_ws" (by simp [postSszNames]))
  have secpOther : (secpState mptMiddle).globals.lookup key = (u256State mptMiddle).globals.lookup key :=
    SecpInitialization.template_other (u256State mptMiddle) 2713718280 key heap (different "secp_accel_scratch" (by simp [postSszNames]))
  have bnOther := BnInitialization.template_other (secpState mptMiddle) 2713718728 key heap
    (different "bn_gamma" (by simp [postSszNames])) (different "bn_b2" (by simp [postSszNames])) (different "bn_expw" (by simp [postSszNames]))
    (by intro name member; exact different name (by simp [postSszNames,member]))
  have blsOther : (blsState middle).globals.lookup key = middle.globals.lookup key :=
    BlsInitialization.template_other middle 2713719944 key heap (different "bls_discount" (by simp [postSszNames])) (different "bls_c" (by simp [postSszNames]))
      (by intro name member; exact different name (by simp [postSszNames,member])) (by intro name member; exact different name (by simp [postSszNames,member]))
  have ripemdOther : (ripemdState middle).globals.lookup key = (blsState middle).globals.lookup key :=
    RipemdInitialization.template_other (blsState middle) 2713729752 key heap (by intro name member; exact different name (by simp [postSszNames,member]))
  have blakeOther : (blakeState middle).globals.lookup key = (ripemdState middle).globals.lookup key :=
    BlakeInitialization.template_other (ripemdState middle) 2713730208 key heap (by intro name member; exact different name (by simp [postSszNames,member]))
  have headerOther : (headerState middle).globals.lookup key = (blakeState middle).globals.lookup key :=
    InitializerAllocations.template_other (blakeState middle) 2713730616 [HeaderInitialization.action] key heap
      (by intro action member; have same := List.mem_singleton.mp member; subst action; exact different "hdr_zero8" (by simp [postSszNames]))
  have bnSame : middle.globals.lookup key = (BnInitialization.template (secpState mptMiddle) 2713718728).globals.lookup key :=
    congrArg (fun globals => globals.lookup key) (globals_of_hash _ middle reached.control)
  have mptSame : mptMiddle.globals.lookup key = (MptInitialization.allocated (sszState source) 2713717456).globals.lookup key :=
    congrArg (fun globals => globals.lookup key) (globals_of_hash _ mptMiddle mpt.control)
  exact headerOther.trans (blakeOther.trans (ripemdOther.trans (blsOther.trans (bnSame.trans (bnOther.trans (secpOther.trans (u256Other.trans (mptSame.trans mptOther))))))))

theorem header_hash_environment (input : Guest.InputBlob) (source mptMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (mpt : MptReached source mptMiddle) (reached : BnReached source mptMiddle middle) :
    Keccak256.Environment (headerState middle) 2713714976#64 2713715176#64 := by
  have installed : OriginalCode.Installed (headerState middle).code := by
    rw [InitializerAllocations.code_of_context middle (headerState middle) (header_context middle),reached.code source mptMiddle middle mpt]
    exact entry.code
  have domain : (headerState middle).memaddrs = InitE.ordinaryDomain :=
    (InitializerAllocations.domain_of_context middle (headerState middle) (header_context middle)).trans (bn_domain input source mptMiddle middle entry mpt reached)
  have mptOracle : mptMiddle.ffi.oracle = (sszState source).ffi.oracle :=
    (oracle_of_hash _ mptMiddle mpt.control).trans (InitializerAllocations.oracle_of_context (sszState source) (MptInitialization.allocated (sszState source) 2713717456)
      (InitializerAllocations.template_context (sszState source) 2713717456 MptInitialization.actions))
  have bnOracle : middle.ffi.oracle = (sszState source).ffi.oracle :=
    (oracle_of_hash _ middle reached.control).trans ((InitializerAllocations.oracle_of_context (secpState mptMiddle) (BnInitialization.template (secpState mptMiddle) 2713718728)
      (BnInitialization.template_context (secpState mptMiddle) 2713718728)).trans
      ((InitializerAllocations.oracle_of_context mptMiddle (secpState mptMiddle) (secp_context mptMiddle)).trans mptOracle))
  have oracle : (headerState middle).ffi.oracle = InitE.sourceOracle :=
    (InitializerAllocations.oracle_of_context middle (headerState middle) (header_context middle)).trans
      (bnOracle.trans (ssz_hash_environment input source entry).hashCode.oracleEq)
  have preserved (name : String) (member : name ∈ ["keccak_st","keccak_pad"]) :
      (headerState middle).globals.lookup (ofString name) = (sszState source).globals.lookup (ofString name) := by
    apply header_from_ssz source mptMiddle middle mpt reached
    intro changed touched
    exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp keccak_globals_preserved_check name member) changed touched)
  exact Keccak256.original_environment (headerState middle) 2713714976#64 2713715176#64 installed domain oracle
    ((preserved "keccak_st" (by simp)).trans (ssz_hash_environment input source entry).stateGlobal)
    ((preserved "keccak_pad" (by simp)).trans (ssz_hash_environment input source entry).scratchGlobal)

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.keccak_globals_preserved_check
#print axioms InitECandidate.Solver.Input.Main.header_from_ssz
#print axioms InitECandidate.Solver.Input.Main.header_hash_environment
