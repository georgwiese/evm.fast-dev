import InitECandidate.Solver.Input.MainBlsEntry
import InitECandidate.Solver.Input.MainBlsInitialization

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

def afterBls : ProgHOL 64 := match afterBn with | .seq _ rest => rest | _ => .skip
def blsState (source : PanSemStateFiniteExact 64 Guest.HostMemory) := {BlsInitialization.template source 2713719944 with clock := source.clock - 22}

theorem after_bn_shape : afterBn = .seq (.call (some (none,none)) (ofString "bls_precompiles_init") []) afterBls := by
  simp only [afterBn,afterSecp,afterU256,afterMpt,afterSsz,afterKeccak,afterSha,afterMemory,body,afterBls,Guest.guestFn_main,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

theorem bls_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) : InitializerAllocations.context (blsState source) = InitializerAllocations.context source :=
  (InitializerAllocations.context_clock (BlsInitialization.template source 2713719944) (source.clock - 22)).trans (BlsInitialization.template_context source 2713719944)

theorem bls_heap (source mptMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory) (reached : BnReached source mptMiddle middle) :
    (blsState middle).globals.lookup (ofString "heap_ptr") = some (.val (.word 2713729752#64)) := BlsInitialization.template_heap middle 2713719944 (reached.heap source mptMiddle middle)

theorem bls_scalars (input : Guest.InputBlob) (source mptMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (mpt : MptReached source mptMiddle) (reached : BnReached source mptMiddle middle) : OriginalScalarGlobals.Scalars (blsState middle).globals :=
  BlsInitialization.template_scalars middle 2713719944 (reached.scalars input source mptMiddle middle entry mpt)

theorem bls_spent (source mptMiddle middle : PanSemStateFiniteExact 64 Guest.HostMemory) (reached : BnReached source mptMiddle middle) (funded : 22 ≤ middle.clock) :
    (blsState middle).clock ≤ source.clock ∧ source.clock - (blsState middle).clock ≤ 469 := by
  have current : (blsState middle).clock = middle.clock - 22 := rfl
  have forward := reached.forward
  have spent := reached.spent
  rw [current]
  omega

private theorem clock_override (source : PanSemStateFiniteExact 64 Guest.HostMemory) (first second : Nat) :
    {{source with clock := first} with clock := second} = {source with clock := second} := rfl

/-- All current BLS entry facts come from the real BN254 continuation.
Funding is forced by the actual terminating main evaluation. -/
theorem bls_prefix (input : Guest.InputBlob) (source mptMiddle middle target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (mpt : MptReached source mptMiddle) (reached : BnReached source mptMiddle middle)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState middle afterBn = (result,target)) (notTimeout : result ≠ some .timeOut) :
    22 ≤ middle.clock ∧ evaluateHOLFiniteState (blsState middle) afterBls = (result,target) := by
  have installed : OriginalCode.Installed middle.code := by rw [reached.code source mptMiddle middle mpt]; exact entry.code
  have scalars := reached.scalars input source mptMiddle middle entry mpt
  have heap := reached.heap source mptMiddle middle
  have discount := bls_entry_zero input source mptMiddle middle entry mpt reached "bls_discount" (by simp [blsEntryNames])
  have constants := bls_entry_zero input source mptMiddle middle entry mpt reached "bls_c" (by simp [blsEntryNames])
  have fp := bls_entry_zero input source mptMiddle middle entry mpt reached "fp_accel_params" (by simp [blsEntryNames])
  have fp2 := bls_entry_zero input source mptMiddle middle entry mpt reached "fp2_accel_params" (by simp [blsEntryNames])
  have g1 := bls_entry_zero input source mptMiddle middle entry mpt reached "bls_g1_accel_params" (by simp [blsEntryNames])
  have domain := bn_domain input source mptMiddle middle entry mpt reached
  have execute (clock : Nat) (enough : 22 ≤ clock) :
      evaluateHOLFiniteState {middle with clock := clock} (.call (some (none,none)) (ofString "bls_precompiles_init") []) =
        (none,{BlsInitialization.template middle 2713719944 with clock := clock - 22}) := by
    have actual := BlsInitialization.call_execute {middle with clock := clock} 2713719944 installed scalars heap discount constants fp fp2 g1 domain (by decide) (by decide) (by decide) enough
    conv_rhs at actual => rw [BlsInitialization.template_clock middle 2713719944 clock,clock_override (BlsInitialization.template middle 2713719944) clock (clock - 22)]
    exact actual
  rw [after_bn_shape] at run
  simpa only [blsState] using terminating_prefix middle target (BlsInitialization.template middle 2713719944) _ afterBls 22 result execute run notTimeout

theorem reached_bls (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (terminates : InitE.sourceBehaviour input = .terminate outcome events) :
    ∃ source mptMiddle middle target result actualOutcome,
      Entry input source ∧ MptReached source mptMiddle ∧ BnReached source mptMiddle middle ∧ 22 ≤ middle.clock ∧
      evaluateHOLFiniteState (blsState middle) afterBls = (result,target) ∧
      (match result with
       | some (.finalFfi event) => actualOutcome = HolOutcome.ffiOutcome event
       | some (.returned _) => actualOutcome = HolOutcome.success
       | _ => False) ∧
      HolBehaviour.terminate outcome events = .terminate actualOutcome target.ffi.ioEvents := by
  obtain ⟨source,mptMiddle,middle,target,result,actualOutcome,entry,mpt,reached,run,classified,observation⟩ := reached_bn input outcome events terminates
  have notTimeout : result ≠ some .timeOut := by intro bad; rw [bad] at classified; cases classified
  obtain ⟨funded,remaining⟩ := bls_prefix input source mptMiddle middle target entry mpt reached result run notTimeout
  exact ⟨source,mptMiddle,middle,target,result,actualOutcome,entry,mpt,reached,funded,remaining,classified,observation⟩

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.after_bn_shape
#print axioms InitECandidate.Solver.Input.Main.bls_context
#print axioms InitECandidate.Solver.Input.Main.bls_heap
#print axioms InitECandidate.Solver.Input.Main.bls_scalars
#print axioms InitECandidate.Solver.Input.Main.bls_spent
#print axioms InitECandidate.Solver.Input.Main.bls_prefix
#print axioms InitECandidate.Solver.Input.Main.reached_bls
