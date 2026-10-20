import InitECandidate.Solver.Input.MainBnEntry
import InitECandidate.Solver.Input.MainBnInitialization

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

def afterBn : ProgHOL 64 := match afterSecp with | .seq _ rest => rest | _ => .skip

theorem after_secp_shape : afterSecp = .seq (.call (some (none,none)) (ofString "bn254_init") []) afterBn := by
  simp only [afterSecp,afterU256,afterMpt,afterSsz,afterKeccak,afterSha,afterMemory,body,afterBn,Guest.guestFn_main,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

structure BnReached (source mptMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  forward : middle.clock ≤ source.clock
  spent : source.clock - middle.clock ≤ 447
  control : KeccakAbsorb.hashControl middle = KeccakAbsorb.hashControl (BnInitialization.template (secpState mptMiddle) 2713718728)

theorem secp_code (source middle : PanSemStateFiniteExact 64 Guest.HostMemory) (reached : MptReached source middle) : (secpState middle).code = source.code :=
  (InitializerAllocations.code_of_context middle (secpState middle) (secp_context middle)).trans (reached.code source middle)

theorem secp_domain (input : Guest.InputBlob) (source middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (reached : MptReached source middle) : (secpState middle).memaddrs = InitE.ordinaryDomain := by
  have same : InitializerAllocations.context (secpState middle) = InitializerAllocations.context (u256State middle) :=
    (InitializerAllocations.context_clock (SecpInitialization.template (u256State middle) 2713718280) (middle.clock - 6)).trans
      (SecpInitialization.template_context (u256State middle) 2713718280)
  exact (InitializerAllocations.domain_of_context (u256State middle) (secpState middle) same).trans (u256_domain input source middle entry reached)

/-- Every terminating continuation reaches the next main suffix through the
real BN254 initializer. Clock padding derives funding from the actual run. -/
theorem bn_prefix (input : Guest.InputBlob) (source mptMiddle target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (reached : MptReached source mptMiddle) (initialFunding : 6 ≤ mptMiddle.clock)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState (secpState mptMiddle) afterSecp = (result,target))
    (notTimeout : result ≠ some .timeOut) :
    ∃ middle,BnReached source mptMiddle middle ∧ evaluateHOLFiniteState middle afterBn = (result,target) := by
  let ready := secpState mptMiddle
  let padded := {ready with clock := ready.clock + 17}
  have installed : OriginalCode.Installed padded.code := by rw [secp_code source mptMiddle reached]; exact entry.code
  obtain ⟨paddedMiddle,prefixRun,_,upper,bounded,control⟩ := BnInitialization.call_execute padded 2713718728 installed
    (secp_scalars input source mptMiddle entry reached) (secp_heap source mptMiddle reached)
    (bn_gamma_before input source mptMiddle entry reached) (bn_params_before input source mptMiddle entry reached)
    (secp_domain input source mptMiddle entry reached) (secp_oracle input source mptMiddle entry reached) (secp_little input source mptMiddle entry reached)
    (by decide) (by decide) (by decide) (by change 17 ≤ ready.clock + 17; omega)
  rw [after_secp_shape] at run
  obtain ⟨funded,_,remaining⟩ := terminating_padded_prefix ready target paddedMiddle _ afterBn 17 result prefixRun run notTimeout
  have previous := secp_spent source mptMiddle reached initialFunding
  change ready.clock ≤ source.clock ∧ source.clock - ready.clock ≤ 430 at previous
  have upper' : paddedMiddle.clock ≤ ready.clock + 17 := upper
  have lower' : ready.clock ≤ paddedMiddle.clock := by
    change ready.clock + 17 - 17 ≤ paddedMiddle.clock at bounded
    simpa using bounded
  refine ⟨{paddedMiddle with clock := paddedMiddle.clock - 17},⟨?_,?_,?_⟩,remaining⟩
  · change paddedMiddle.clock - 17 ≤ source.clock
    omega
  · change source.clock - (paddedMiddle.clock - 17) ≤ 447
    omega
  · have model := BnInitialization.template_clock ready 2713718728 padded.clock
    change BnInitialization.template padded 2713718728 = _ at model
    rw [model] at control
    exact control.trans (KeccakAbsorb.hashControl_clock (BnInitialization.template ready 2713718728) padded.clock)

theorem reached_bn (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (terminates : InitE.sourceBehaviour input = .terminate outcome events) :
    ∃ source mptMiddle middle target result actualOutcome,
      Entry input source ∧ MptReached source mptMiddle ∧ BnReached source mptMiddle middle ∧
      evaluateHOLFiniteState middle afterBn = (result,target) ∧
      (match result with
       | some (.finalFfi event) => actualOutcome = HolOutcome.ffiOutcome event
       | some (.returned _) => actualOutcome = HolOutcome.success
       | _ => False) ∧
      HolBehaviour.terminate outcome events = .terminate actualOutcome target.ffi.ioEvents := by
  obtain ⟨source,mptMiddle,target,result,actualOutcome,entry,reached,funded,run,classified,observation⟩ := reached_secp input outcome events terminates
  have notTimeout : result ≠ some .timeOut := by intro bad; rw [bad] at classified; cases classified
  obtain ⟨middle,metadata,remaining⟩ := bn_prefix input source mptMiddle target entry reached funded result run notTimeout
  exact ⟨source,mptMiddle,middle,target,result,actualOutcome,entry,reached,metadata,remaining,classified,observation⟩

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.after_secp_shape
#print axioms InitECandidate.Solver.Input.Main.secp_code
#print axioms InitECandidate.Solver.Input.Main.secp_domain
#print axioms InitECandidate.Solver.Input.Main.bn_prefix
#print axioms InitECandidate.Solver.Input.Main.reached_bn
