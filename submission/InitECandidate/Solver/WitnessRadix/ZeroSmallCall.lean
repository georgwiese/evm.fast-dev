import InitECandidate.Solver.WitnessRadix.ZeroSmall
import InitECandidate.Solver.WitnessRadix.ZeroEnvironment

namespace InitECandidate.Solver.WitnessRadix.Zero
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem memoryByte_away (memory : WordWrites.Memory) (be : Bool) (dst query : BitVec 64) (index remaining : Nat)
    (away : ∀ offset < remaining, query ≠ panByteAlignHOL (width := 64) (byteAddress dst (index + offset))) :
    memoryByte memory be dst index remaining query = memory query := by
  induction remaining generalizing memory index with
  | zero => rfl
  | succ remaining ih =>
    rw [memoryByte, ih]
    · have distinct := away 0 (by omega)
      have distinct' : query ≠ panByteAlignHOL (width := 64) (dst + BitVec.ofNat 64 index) := by
        simpa only [Nat.add_zero, byteAddress] using distinct
      exact if_neg distinct'
    · intro offset inside
      have distinct := away (1 + offset) (by omega)
      simpa only [Nat.add_assoc] using distinct

theorem small_memory_away (memory : WordWrites.Memory) (be : Bool) (dst query : BitVec 64) (length : Nat)
    (short : length < 8) (aligned : dst.toNat % 8 = 0) (fits : dst.toNat + 32 < 2 ^ 64)
    (away : query ≠ dst) : memoryByte memory be dst 0 length query = memory query := by
  apply memoryByte_away
  intro offset inside
  rw [Nat.zero_add, small_offset dst offset (by omega) aligned fits]
  exact away

/-- Actual memzero call for short ranges, including cap=4, with no assumed
byte-store oracle. It restores caller locals and consumes length+1 clocks. -/
theorem call_small {F : Type} (source : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (dst : BitVec 64) (length : Nat)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      arguments = some (values dst length))
    (code : source.code.lookup (ofString "memzero") = some (formals, body, .one))
    (short : length < 8) (aligned : dst.toNat % 8 = 0) (fits : dst.toNat + 32 < 2 ^ 64)
    (mapped : source.memaddrs dst) (enough : length + 1 ≤ source.clock) :
    evaluateHOLFiniteState source (.call (some (none, none)) (ofString "memzero") arguments) =
      (none, { source with memory := memoryByte source.memory source.be dst 0 length, clock := source.clock - (length + 1) }) := by
  classical
  obtain ⟨callee, lookup, dstLocal, lengthLocal⟩ := environment source.code.lookup dst length code
  let entry := callEntryStateHOLFinite source callee
  have run := execute_small entry dst length short aligned fits dstLocal lengthLocal mapped
    (by change length ≤ source.clock - 1; omega)
  have frame := small_final_frame entry dst length
  have callRun := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "memzero")
    arguments (values dst length) body callee .one (.val (.word 0#64)) (smallFinalState entry dst length)
    args lookup (by omega) run (by simp [shapeEqHOL, shapeOfHOLExact])
  have restored := congrArg (fun state : PanSemStateFiniteExact 64 F => { state with locals := source.locals }) frame
  have clockEq : source.clock - 1 - length = source.clock - (length + 1) := by omega
  simpa only [emptyLocalsHOLFinite, entry, callEntryStateHOLFinite, clockEq] using callRun.trans
    (congrArg (fun state : PanSemStateFiniteExact 64 F => (none, state)) restored)

end InitECandidate.Solver.WitnessRadix.Zero

#print axioms InitECandidate.Solver.WitnessRadix.Zero.small_memory_away
#print axioms InitECandidate.Solver.WitnessRadix.Zero.call_small
