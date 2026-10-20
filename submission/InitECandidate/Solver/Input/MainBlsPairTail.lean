import InitECandidate.Solver.Input.MainBlsLayout

namespace InitECandidate.Solver.Input.Main.BlsInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def pairTemplate (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :=
  BlsPairInitialization.template (BlsPairInitialization.template source cursor .fp2) (cursor + 192) .g1

theorem pair_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor clock : Nat) :
    pairTemplate {source with clock := clock} cursor = {pairTemplate source cursor with clock := clock} := by
  unfold pairTemplate
  rw [BlsPairInitialization.template_clock source cursor .fp2 clock]
  exact BlsPairInitialization.template_clock (BlsPairInitialization.template source cursor .fp2) (cursor + 192) .g1 clock

/-- Actual final two BLS library calls, with the second guard and heap derived
from the first call's concrete global frame. -/
theorem pair_tail_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (constants : BitVec 64)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (fp2Zero : source.globals.lookup (ofString "fp2_accel_params") = some (.val (.word 0#64)))
    (g1Zero : source.globals.lookup (ofString "bls_g1_accel_params") = some (.val (.word 0#64)))
    (binding : source.globals.lookup (ofString "bls_c") = some (.val (.word constants))) (nonzero : constants ≠ 0#64)
    (room : cursor + 384 ≤ 33806089496) (aligned : cursor % 8 = 0) (enough : 6 ≤ source.clock) :
    evaluateHOLFiniteState source afterFp = (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite {pairTemplate source cursor with clock := source.clock - 6}) := by
  have firstRun := BlsPairInitialization.call_execute source cursor .fp2 constants installed scalars heap fp2Zero binding nonzero (by omega) aligned (by omega)
  let first := {BlsPairInitialization.template source cursor .fp2 with clock := source.clock - 3}
  have context : InitializerAllocations.context first = InitializerAllocations.context source :=
    (InitializerAllocations.context_clock (BlsPairInitialization.template source cursor .fp2) (source.clock - 3)).trans (BlsPairInitialization.template_context source cursor .fp2)
  have firstInstalled := InitializerAllocations.installed_of_context source first context installed
  have firstScalars := BlsPairInitialization.template_scalars source cursor .fp2 scalars
  have firstHeap := BlsPairInitialization.template_heap source cursor .fp2 heap
  have firstZero : first.globals.lookup (ofString "bls_g1_accel_params") = some (.val (.word 0#64)) :=
    (BlsPairInitialization.template_other_fields source cursor .fp2 (ofString "bls_g1_accel_params") (by decide) (by decide) (by decide) (by decide)).trans g1Zero
  have firstConstants : first.globals.lookup (ofString "bls_c") = some (.val (.word constants)) := (BlsPairInitialization.template_constants source cursor .fp2).trans binding
  have secondRun := BlsPairInitialization.call_execute first (cursor + 192) .g1 constants firstInstalled firstScalars firstHeap firstZero firstConstants nonzero
    (by omega) (by omega) (by change 3 ≤ source.clock - 3; omega)
  have clock : source.clock - 3 - 3 = source.clock - 6 := by omega
  have second : evaluateHOLFiniteState first g1Call = (none,{pairTemplate source cursor with clock := source.clock - 6}) := by
    simpa only [g1Call,BlsPairInitialization.function,first,BlsPairInitialization.template_clock,clock,pairTemplate] using secondRun
  rw [afterFp,StateSteps.next_sequence source first fp2Call _ firstRun (by change source.clock - 3 ≤ source.clock; omega),
    afterFp2,StateSteps.next_sequence first {pairTemplate source cursor with clock := source.clock - 6} g1Call _ second (by change source.clock - 6 ≤ source.clock - 3; omega)]
  exact BuildEntry.zero_return {pairTemplate source cursor with clock := source.clock - 6}

end InitECandidate.Solver.Input.Main.BlsInitialization

#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.pair_clock
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.pair_tail_execute
