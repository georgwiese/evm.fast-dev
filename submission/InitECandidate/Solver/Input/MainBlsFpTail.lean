import InitECandidate.Solver.Input.MainBlsPairTail

namespace InitECandidate.Solver.Input.Main.BlsInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def afterConstantsTemplate (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (constants : BitVec 64) :=
  pairTemplate (BlsFpInitialization.template source cursor constants) (cursor + 240)

theorem after_constants_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (constants : BitVec 64) (clock : Nat) :
    afterConstantsTemplate {source with clock := clock} cursor constants = {afterConstantsTemplate source cursor constants with clock := clock} := by
  unfold afterConstantsTemplate
  rw [BlsFpInitialization.template_clock source cursor constants clock]
  exact pair_clock (BlsFpInitialization.template source cursor constants) (cursor + 240) clock

private theorem fp_pair_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (constants : BitVec 64) (kind : BlsPairInitialization.Kind) :
    (BlsFpInitialization.template source cursor constants).globals.lookup (ofString (BlsPairInitialization.paramsName kind)) = source.globals.lookup (ofString (BlsPairInitialization.paramsName kind)) := by
  apply BlsFpInitialization.template_other source cursor constants _ (by cases kind <;> decide)
  intro name member
  simp only [BlsFpInitialization.symbols,List.mem_cons,List.not_mem_nil,or_false] at member
  cases kind
  all_goals rcases member with rfl | rfl | rfl | rfl | rfl <;> decide

/-- Real FP, FP2 and G1 initialization suffix. Current guards, mapped constant
bytes and aggregate room supply all three executions. -/
theorem fp_tail_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (constants : BitVec 64)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (fpZero : source.globals.lookup (ofString "fp_accel_params") = some (.val (.word 0#64)))
    (fp2Zero : source.globals.lookup (ofString "fp2_accel_params") = some (.val (.word 0#64)))
    (g1Zero : source.globals.lookup (ofString "bls_g1_accel_params") = some (.val (.word 0#64)))
    (binding : source.globals.lookup (ofString "bls_c") = some (.val (.word constants))) (nonzero : constants ≠ 0#64)
    (domain : source.memaddrs = InitE.ordinaryDomain) (constantArena : AllocatedBytes.Arena constants 7136) (constantAligned : constants.toNat % 8 = 0)
    (lower : 2701131776 ≤ cursor) (room : cursor + 624 ≤ 33806089496) (aligned : cursor % 8 = 0) (enough : 17 ≤ source.clock) :
    evaluateHOLFiniteState source afterConstants =
      (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite {afterConstantsTemplate source cursor constants with clock := source.clock - 17}) := by
  have firstRun := BlsFpInitialization.call_execute source cursor constants installed scalars heap fpZero binding nonzero domain constantArena constantAligned lower (by omega) aligned (by omega)
  let first := {BlsFpInitialization.template source cursor constants with clock := source.clock - 11}
  have context : InitializerAllocations.context first = InitializerAllocations.context source :=
    (InitializerAllocations.context_clock (BlsFpInitialization.template source cursor constants) (source.clock - 11)).trans (BlsFpInitialization.template_context source cursor constants)
  have firstInstalled := InitializerAllocations.installed_of_context source first context installed
  have firstGlobals : first.globals = (BlsFpInitialization.template source cursor constants).globals := by simp only [first]
  have firstScalars : OriginalScalarGlobals.Scalars first.globals := by rw [firstGlobals]; exact BlsFpInitialization.template_scalars source cursor constants scalars
  have firstHeap : first.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 240)))) := by rw [firstGlobals]; exact BlsFpInitialization.template_heap source cursor constants heap
  have firstFp2 : first.globals.lookup (ofString "fp2_accel_params") = some (.val (.word 0#64)) := by rw [firstGlobals]; exact (fp_pair_other source cursor constants .fp2).trans fp2Zero
  have firstG1 : first.globals.lookup (ofString "bls_g1_accel_params") = some (.val (.word 0#64)) := by rw [firstGlobals]; exact (fp_pair_other source cursor constants .g1).trans g1Zero
  have firstConstants : first.globals.lookup (ofString "bls_c") = some (.val (.word constants)) := by rw [firstGlobals]; exact (BlsFpInitialization.template_constants source cursor constants).trans binding
  have tailRun := pair_tail_execute first (cursor + 240) constants firstInstalled firstScalars firstHeap firstFp2 firstG1 firstConstants nonzero
    (by omega) (by omega) (by change 6 ≤ source.clock - 11; omega)
  rw [afterConstants,StateSteps.next_sequence source first fpCall afterFp firstRun (by change source.clock - 11 ≤ source.clock; omega)]
  have clock : source.clock - 11 - 6 = source.clock - 17 := by omega
  simpa only [first,pair_clock,clock,afterConstantsTemplate] using tailRun

end InitECandidate.Solver.Input.Main.BlsInitialization

#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.after_constants_clock
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.fp_tail_execute
