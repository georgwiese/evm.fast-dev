import InitECandidate.Solver.WitnessRadix.KeccakAbsorbTarget
import InitECandidate.Solver.WitnessRadix.KeccakAbsorbEnvironment

namespace InitECandidate.Solver.WitnessRadix.KeccakAbsorb
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 10000

/-- Actual fixed block-absorption call from its real ABI/code/oracle and
mapped data. It restores caller locals, spends exactly 19 source clocks,
and preserves all cells outside the 200-byte state footprint. -/
theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64)) (stp blk : BitVec 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (values stp blk))
    (code : source.code.lookup (ofString "keccak_absorb_block") = some (formals,body,.one))
    (permCode : source.code.lookup (ofString "keccak_f1600") = some (Keccak.formals,Keccak.f1600Body,.one))
    (oracleEq : source.ffi.oracle = InitE.sourceOracle) (aligned : stp.toNat%8=0) (fits : stp.toNat+200<2^64)
    (mapped : Mapped source stp blk (isUnaligned blk)) (enough : 19 ≤ source.clock) :
    ∃ output : PanSemStateFiniteExact 64 Guest.HostMemory,
      evaluateHOLFiniteState source (.call (some (none,none)) (ofString "keccak_absorb_block") arguments) = (none,output) ∧
      output.locals = source.locals ∧ output.clock = source.clock-19 ∧ hashControl output = hashControl source ∧
      ∀ query : BitVec 64, Away stp query → output.memory query = source.memory query := by
  classical
  obtain ⟨callee,lookup,stpLocal,blkLocal⟩ := environment source.code.lookup stp blk code
  let entry := callEntryStateHOLFinite source callee
  have entryMapped : Mapped entry stp blk (isUnaligned blk) := ⟨mapped.stateWords,mapped.blockWords,mapped.blockBytes⟩
  obtain ⟨bytes,length,run⟩ := execute entry stp blk stpLocal blkLocal entryMapped permCode oracleEq aligned fits
    (by change 18 ≤ source.clock-1; omega)
  let output := { target entry stp blk bytes with locals := source.locals }
  have callRun := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "keccak_absorb_block") arguments
    (values stp blk) body callee .one (.val (.word 0#64)) (target entry stp blk bytes) args lookup (by omega) run
    (by simp [shapeEqHOL,shapeOfHOLExact])
  refine ⟨output,callRun,rfl,?_,?_,?_⟩
  · change (target entry stp blk bytes).clock = source.clock-19
    rw [target_clock]
    change source.clock-1-18 = source.clock-19
    omega
  · have h := target_control entry stp blk bytes
    exact h
  · intro query away
    exact target_memory_away entry stp blk query bytes away

end InitECandidate.Solver.WitnessRadix.KeccakAbsorb

#print axioms InitECandidate.Solver.WitnessRadix.KeccakAbsorb.call_execute
