import InitECandidate.Solver.WitnessRadix.CopyGeneralRegionAgreement
import InitECandidate.Solver.WitnessRadix.Keccak256Output

namespace InitECandidate.Solver.WitnessRadix.Keccak256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact MemoryRegion
open Flapjack.Basis.Pure.MlString QueryBranch

theorem outMemoryMany_agrees (region : BitVec 64 → Prop) (left right : WordWrites.Memory)
    (same : Agree region left right) (stp out : BitVec 64) (offsets : List Nat)
    (reads : ∀ offset ∈ offsets, region (byteAddress stp offset)) :
    Agree region (outMemoryMany left stp out offsets) (outMemoryMany right stp out offsets) := by
  induction offsets generalizing left right with
  | nil => exact same
  | cons offset rest ih =>
    have readEq := same _ (reads offset (by simp))
    have next := MemoryRegion.word_put region left right same (byteAddress out offset)
      (MemoryBytes.wordBits (right (byteAddress stp offset)))
    have nextSame : Agree region (outMemory left stp out offset) (outMemory right stp out offset) := by
      simpa only [outMemory, readEq] using next
    exact ih _ _ nextSame (by intro offset member; exact reads offset (List.mem_cons_of_mem _ member))

def outputState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp out : BitVec 64) :
    PanSemStateFiniteExact 64 Guest.HostMemory :=
  if out &&& 7#64 = 0#64 then { source with memory := outMemoryMany source.memory stp out [0,8,16,24] }
  else CopyGeneral.callState source stp out 32

theorem outputState_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp out : BitVec 64) :
    (outputState source stp out).locals = source.locals := by unfold outputState; split <;> rfl

theorem outputState_ffi (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp out : BitVec 64) :
    (outputState source stp out).ffi = source.ffi := by unfold outputState; split <;> rfl

theorem outputState_control (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp out : BitVec 64) :
    KeccakAbsorb.hashControl (outputState source stp out) = KeccakAbsorb.hashControl source := by
  unfold outputState
  split <;> rfl

theorem outputState_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp out : BitVec 64) :
    (outputState source stp out).clock ≤ source.clock ∧
      source.clock - 33 ≤ (outputState source stp out).clock := by
  have bound := CopyGeneral.cost_le stp out 32
  unfold outputState
  split
  · exact ⟨Nat.le_refl _, Nat.sub_le _ _⟩
  · change source.clock - (CopyGeneral.cost stp out 32 + 1) ≤ source.clock ∧
      source.clock - 33 ≤ source.clock - (CopyGeneral.cost stp out 32 + 1)
    omega

theorem outputState_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp out : BitVec 64)
    (stpLocal : source.locals.lookup (ofString "stp") = some (.val (.word stp)))
    (outLocal : source.locals.lookup (ofString "out") = some (.val (.word out)))
    (mapped : OutMapped source stp out)
    (code : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (enough : 33 ≤ source.clock) :
    evaluateHOLFiniteState source outProgram = (none, outputState source stp out) := by
  classical
  have read := output_alignment_read source out outLocal
  simp only [eval] at read
  by_cases mask : out &&& 7#64 = 0#64
  · have run := out_words_execute source stp out stpLocal outLocal mapped.stateWords (mapped.outputWords mask)
    rw [outProgram, evaluateHOLFiniteState_ite, read]
    simpa [mask, outputState] using run
  · have args : evalListHOLFinite source
        (h := fun query => Classical.propDecidable (source.memaddrs query))
        [localVar "out", localVar "stp", .const 32#64] = some (CopyGeneral.values out stp 32) := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, localVar, toExact, outLocal, stpLocal, CopyGeneral.values]
    have bound := CopyGeneral.cost_le stp out 32
    have run := CopyGeneral.call_execute source [localVar "out", localVar "stp", .const 32#64]
      stp out 32 args code mapped.copy (by decide) (by omega)
    rw [outProgram, evaluateHOLFiniteState_ite, read]
    simpa [mask, outputState, outCopy] using run

theorem outputState_memory_agrees (source right : PanSemStateFiniteExact 64 Guest.HostMemory)
    (endian : source.be = right.be) (region : BitVec 64 → Prop)
    (same : Agree region source.memory right.memory) (stp out : BitVec 64)
    (wordReads : ∀ offset < 32, offset % 8 = 0 → region (byteAddress stp offset))
    (byteReads : ∀ offset < 32,
      region (panByteAlignHOL (width := 64) (byteAddress stp offset))) :
    Agree region (outputState source stp out).memory (outputState right stp out).memory := by
  unfold outputState
  split
  · apply outMemoryMany_agrees region source.memory right.memory same stp out [0,8,16,24]
    intro offset member
    simp at member
    rcases member with rfl | rfl | rfl | rfl <;> exact wordReads _ (by decide) (by decide)
  · have agreement := CopyGeneral.resultMemory_agrees region source.memory right.memory same right.be stp out 32
      (by intro mask; exact wordReads) byteReads
    simpa only [CopyGeneral.callState, endian] using agreement

theorem outputState_memory_away (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (stp out query : BitVec 64) (away : CopyGeneral.Away out query 32) :
    (outputState source stp out).memory query = source.memory query := by
  unfold outputState
  split
  · apply out_memory_away
    intro offset member
    simp at member
    rcases member with rfl | rfl | rfl | rfl <;> exact (away _ (by decide)).1
  · exact CopyGeneral.call_memory_away source stp out query 32 away

end InitECandidate.Solver.WitnessRadix.Keccak256

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.outMemoryMany_agrees
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.outputState_locals
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.outputState_ffi
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.outputState_control
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.outputState_clock
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.outputState_execute
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.outputState_memory_agrees
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.outputState_memory_away
