import InitECandidate.Solver.Input.MainEvmEntry
import InitECandidate.Solver.Input.MainEvmInitialization
import InitECandidate.Solver.Input.MainEvmFields

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def afterEvm : ProgHOL 64 := match afterHeader with | .seq _ rest => rest | _ => .skip

theorem after_header_shape : afterHeader = .seq (.call (some (none,none)) (ofString "evm_init") []) afterEvm := by
  simp only [afterHeader,afterBlake,afterRipemd,afterBls,afterBn,afterSecp,afterU256,afterMpt,afterSsz,afterKeccak,afterSha,afterMemory,body,afterEvm,
    Guest.guestFn_main,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

structure EvmReached (source bnMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  forward : middle.clock ≤ source.clock
  spent : source.clock - middle.clock ≤ 721
  control : KeccakAbsorb.hashControl middle = KeccakAbsorb.hashControl (EvmInitialization.template (headerState bnMiddle) 2713730624)

private theorem evm_at_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor clock : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (stp pad : BitVec 64) (environment : Keccak256.Environment source stp pad)
    (stateArena : AllocatedBytes.Arena stp 200) (stateAligned : stp.toNat % 8 = 0)
    (padArena : AllocatedBytes.Arena pad 136) (padAligned : pad.toNat % 8 = 0)
    (lower : 2701131776 ≤ cursor) (room : cursor + 216 ≤ 33806089496) (aligned : cursor % 8 = 0) (enough : 239 ≤ clock) :
    ∃ post,evaluateHOLFiniteState {source with clock := clock} (.call (some (none,none)) (ofString "evm_init") []) = (none,post) ∧
      post.clock ≤ clock ∧ clock - 239 ≤ post.clock ∧
      KeccakAbsorb.hashControl post = KeccakAbsorb.hashControl (EvmInitialization.template source cursor) := by
  have clockEnvironment := environment.of_control source {source with clock := clock} stp pad rfl
  obtain ⟨post,run,_,upper,lowerBound,control⟩ := EvmInitialization.call_execute {source with clock := clock} cursor installed scalars heap stp pad clockEnvironment
    stateArena stateAligned padArena padAligned lower room aligned enough
  have model := EvmInitialization.template_clock source cursor clock
  rw [model] at control
  exact ⟨post,run,upper,lowerBound,control.trans (KeccakAbsorb.hashControl_clock (EvmInitialization.template source cursor) clock)⟩

/-- Termination of actual main supplies the EVM initializer's funding.
Its reached state retains the real overlapping hash and all preceding events. -/
theorem evm_prefix (input : Guest.InputBlob) (source mptMiddle bnMiddle target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (mpt : MptReached source mptMiddle) (bn : BnReached source mptMiddle bnMiddle) (initialFunding : 35 ≤ bnMiddle.clock)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState (headerState bnMiddle) afterHeader = (result,target)) (notTimeout : result ≠ some .timeOut) :
    ∃ middle,EvmReached source bnMiddle middle ∧ evaluateHOLFiniteState middle afterEvm = (result,target) := by
  let ready := headerState bnMiddle
  have environment := header_hash_environment input source mptMiddle bnMiddle entry mpt bn
  have installed : OriginalCode.Installed ready.code :=
    InitializerAllocations.installed_of_context bnMiddle ready (header_context bnMiddle) (by rw [bn.code source mptMiddle bnMiddle mpt]; exact entry.code)
  obtain ⟨paddedMiddle,prefixRun,upper,lowerBound,control⟩ := evm_at_clock ready 2713730624 (ready.clock + 239) installed
    (header_scalars input source mptMiddle bnMiddle entry mpt bn) (header_heap source mptMiddle bnMiddle bn) 2713714976#64 2713715176#64 environment
    ⟨by decide,by decide⟩ (by decide) ⟨by decide,by decide⟩ (by decide) (by decide) (by decide) (by decide) (by omega)
  rw [after_header_shape] at run
  obtain ⟨funded,_,remaining⟩ := terminating_padded_prefix ready target paddedMiddle _ afterEvm 239 result prefixRun run notTimeout
  have previous := header_spent source mptMiddle bnMiddle bn initialFunding
  change ready.clock ≤ source.clock ∧ source.clock - ready.clock ≤ 482 at previous
  have lower' : ready.clock ≤ paddedMiddle.clock := by simpa only [Nat.add_sub_cancel_right] using lowerBound
  refine ⟨{paddedMiddle with clock := paddedMiddle.clock - 239},⟨?_,?_,?_⟩,remaining⟩
  · change paddedMiddle.clock - 239 ≤ source.clock
    omega
  · change source.clock - (paddedMiddle.clock - 239) ≤ 721
    omega
  · exact control

theorem reached_evm (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (terminates : InitE.sourceBehaviour input = .terminate outcome events) :
    ∃ source mptMiddle bnMiddle middle target result actualOutcome,
      Entry input source ∧ MptReached source mptMiddle ∧ BnReached source mptMiddle bnMiddle ∧ EvmReached source bnMiddle middle ∧
      evaluateHOLFiniteState middle afterEvm = (result,target) ∧
      (match result with
       | some (.finalFfi event) => actualOutcome = HolOutcome.ffiOutcome event
       | some (.returned _) => actualOutcome = HolOutcome.success
       | _ => False) ∧
      HolBehaviour.terminate outcome events = .terminate actualOutcome target.ffi.ioEvents := by
  obtain ⟨source,mptMiddle,bnMiddle,target,result,actualOutcome,entry,mpt,bn,funded,run,classified,observation⟩ := reached_header input outcome events terminates
  have notTimeout : result ≠ some .timeOut := by intro bad; rw [bad] at classified; cases classified
  obtain ⟨middle,metadata,remaining⟩ := evm_prefix input source mptMiddle bnMiddle target entry mpt bn funded result run notTimeout
  exact ⟨source,mptMiddle,bnMiddle,middle,target,result,actualOutcome,entry,mpt,bn,metadata,remaining,classified,observation⟩

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.after_header_shape
#print axioms InitECandidate.Solver.Input.Main.evm_prefix
#print axioms InitECandidate.Solver.Input.Main.reached_evm
