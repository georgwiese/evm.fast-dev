import InitECandidate.Solver.Input.MainU256Prefix
import InitECandidate.Solver.Input.MainSecpProgram

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

private theorem hash_domain (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    (KeccakAbsorb.hashControl source).memaddrs = source.memaddrs := rfl

theorem u256_code (source middle : PanSemStateFiniteExact 64 Guest.HostMemory) (reached : MptReached source middle) :
    (u256State middle).code = source.code :=
  ((InitializerAllocations.context_code (u256State middle)).symm.trans
    ((congrArg (fun s => s.code) (u256_context middle)).trans (InitializerAllocations.context_code middle))).trans (reached.code source middle)

theorem u256_domain (input : Guest.InputBlob) (source middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (reached : MptReached source middle) :
    (u256State middle).memaddrs = InitE.ordinaryDomain := by
  let allocated := MptInitialization.allocated (sszState source) 2713717456
  have actual : middle.memaddrs = allocated.memaddrs :=
    (hash_domain middle).symm.trans ((congrArg (fun s => s.memaddrs) reached.control).trans (hash_domain allocated))
  have allocation : allocated.memaddrs = (sszState source).memaddrs :=
    (InitializerAllocations.context_domain allocated).symm.trans
      ((congrArg (fun s => s.memaddrs) (InitializerAllocations.template_context (sszState source) 2713717456 MptInitialization.actions)).trans
        (InitializerAllocations.context_domain (sszState source)))
  have workspace : (u256State middle).memaddrs = middle.memaddrs :=
    (InitializerAllocations.context_domain (u256State middle)).symm.trans
      ((congrArg (fun s => s.memaddrs) (u256_context middle)).trans (InitializerAllocations.context_domain middle))
  exact workspace.trans (actual.trans (allocation.trans (ssz_hash_environment input source entry).domain))

theorem secp_scratch_before (input : Guest.InputBlob) (source middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (reached : MptReached source middle) :
    (u256State middle).globals.lookup (ofString "secp_accel_scratch") = some (.val (.word 0#64)) := by
  have workspace : (u256State middle).globals.lookup (ofString "secp_accel_scratch") = middle.globals.lookup (ofString "secp_accel_scratch") := by
    apply InitializerAllocations.template_other middle 2713717640 U256Initialization.actions _ (by decide)
    intro action member
    simp only [U256Initialization.actions,List.mem_cons,List.not_mem_nil,or_false] at member
    subst action
    decide
  rw [workspace]
  have globals := congrArg (fun s : PanSemStateFiniteExact 64 Guest.HostMemory => s.globals) reached.control
  change middle.globals = (MptInitialization.allocated (sszState source) 2713717456).globals at globals
  rw [globals]
  have mpt := MptInitialization.allocated_other (sszState source) 2713717456 (ofString "secp_accel_scratch") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have ssz := SszInitialization.template_other (keccakState source) 2713715312 (ofString "secp_accel_scratch") (by decide) (by decide) (by decide) (by decide)
  have keccak := KeccakInitialization.template_other (shaState source) 2713714976 (ofString "secp_accel_scratch") (by decide) (by decide) (by decide)
  have sha := ShaInitialization.template_other (memoryState source) 2713714688 (ofString "secp_accel_scratch") (by decide) (by decide) (by decide) (by decide)
  have memory := memory_other source (ofString "secp_accel_scratch") (by decide) (by decide) (by decide)
  exact mpt.trans (ssz.trans (keccak.trans (sha.trans (memory.trans (entry.zeros _ SecpInitialization.scratch_member)))))

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.u256_code
#print axioms InitECandidate.Solver.Input.Main.u256_domain
#print axioms InitECandidate.Solver.Input.Main.secp_scratch_before
