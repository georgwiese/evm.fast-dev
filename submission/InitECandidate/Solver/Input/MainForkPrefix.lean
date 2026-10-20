import InitECandidate.Solver.Input.MainForkEntry
import InitECandidate.Solver.Input.MainForkFields

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def afterFork : ProgHOL 64 := match afterEvm with | .seq _ rest => rest | _ => .skip

theorem after_evm_shape : afterEvm = .seq (.call (some (none,none)) (ofString "fork_init") []) afterFork := by
  simp only [afterEvm,afterHeader,afterBlake,afterRipemd,afterBls,afterBn,afterSecp,afterU256,afterMpt,afterSsz,afterKeccak,afterSha,afterMemory,body,afterFork,
    Guest.guestFn_main,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

structure ForkReached (source evmMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  forward : middle.clock ≤ source.clock
  spent : source.clock - middle.clock ≤ 832
  control : KeccakAbsorb.hashControl middle = KeccakAbsorb.hashControl (ForkInitialization.template evmMiddle 2713730840)

theorem fork_prefix (input : Guest.InputBlob) (source mptMiddle bnMiddle evmMiddle target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (mpt : MptReached source mptMiddle) (bn : BnReached source mptMiddle bnMiddle) (evm : EvmReached source bnMiddle evmMiddle)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState evmMiddle afterEvm = (result,target)) (notTimeout : result ≠ some .timeOut) :
    ∃ middle,ForkReached source evmMiddle middle ∧ evaluateHOLFiniteState middle afterFork = (result,target) := by
  let padded := {evmMiddle with clock := evmMiddle.clock + 111}
  have installed : OriginalCode.Installed padded.code := by rw [evm.code source mptMiddle bnMiddle evmMiddle mpt bn]; exact entry.code
  obtain ⟨paddedMiddle,prefixRun,_,upper,bounded,control⟩ := ForkInitialization.call_execute padded 2713730840 installed
    (evm.scalars input source mptMiddle bnMiddle evmMiddle entry mpt bn) (evm.heap source mptMiddle bnMiddle evmMiddle bn)
    (evm.domain input source mptMiddle bnMiddle evmMiddle entry mpt bn) (by decide) (by decide) (by decide) (by change 111 ≤ evmMiddle.clock + 111; omega)
  rw [after_evm_shape] at run
  obtain ⟨funded,_,remaining⟩ := terminating_padded_prefix evmMiddle target paddedMiddle _ afterFork 111 result prefixRun run notTimeout
  have previous := evm.spent
  have previousForward := evm.forward
  have upper' : paddedMiddle.clock ≤ evmMiddle.clock + 111 := upper
  have lower' : evmMiddle.clock ≤ paddedMiddle.clock := by simpa only [padded,Nat.add_sub_cancel_right] using bounded
  refine ⟨{paddedMiddle with clock := paddedMiddle.clock - 111},⟨?_,?_,?_⟩,remaining⟩
  · change paddedMiddle.clock - 111 ≤ source.clock
    omega
  · change source.clock - (paddedMiddle.clock - 111) ≤ 832
    omega
  · have model := ForkInitialization.template_clock evmMiddle 2713730840 padded.clock
    change ForkInitialization.template padded 2713730840 = _ at model
    rw [model] at control
    exact control.trans (KeccakAbsorb.hashControl_clock (ForkInitialization.template evmMiddle 2713730840) padded.clock)

theorem reached_fork (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (terminates : InitE.sourceBehaviour input = .terminate outcome events) :
    ∃ source mptMiddle bnMiddle evmMiddle middle target result actualOutcome,
      Entry input source ∧ MptReached source mptMiddle ∧ BnReached source mptMiddle bnMiddle ∧ EvmReached source bnMiddle evmMiddle ∧ ForkReached source evmMiddle middle ∧
      evaluateHOLFiniteState middle afterFork = (result,target) ∧
      (match result with
       | some (.finalFfi event) => actualOutcome = HolOutcome.ffiOutcome event
       | some (.returned _) => actualOutcome = HolOutcome.success
       | _ => False) ∧
      HolBehaviour.terminate outcome events = .terminate actualOutcome target.ffi.ioEvents := by
  obtain ⟨source,mptMiddle,bnMiddle,evmMiddle,target,result,actualOutcome,entry,mpt,bn,evm,run,classified,observation⟩ := reached_evm input outcome events terminates
  have notTimeout : result ≠ some .timeOut := by intro bad; rw [bad] at classified; cases classified
  obtain ⟨middle,metadata,remaining⟩ := fork_prefix input source mptMiddle bnMiddle evmMiddle target entry mpt bn evm result run notTimeout
  exact ⟨source,mptMiddle,bnMiddle,evmMiddle,middle,target,result,actualOutcome,entry,mpt,bn,evm,metadata,remaining,classified,observation⟩

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.after_evm_shape
#print axioms InitECandidate.Solver.Input.Main.fork_prefix
#print axioms InitECandidate.Solver.Input.Main.reached_fork
