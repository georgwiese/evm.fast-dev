import InitECandidate.Solver.WitnessRadix.Keccak256PairedCall

namespace InitECandidate.Solver.WitnessRadix.Keccak256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact MemoryRegion
open Flapjack.Basis.Pure.MlString

/-- A public region contains each buffer's raw and aligned memory cells.
It need not contain any of either program's private table allocations. -/
structure BufferRegion (region : BitVec 64 → Prop) (stp pointer scratch out : BitVec 64) (length : Nat) : Prop where
  state : ∀ offset < 200, region (byteAddress stp offset) ∧
    region (panByteAlignHOL (width := 64) (byteAddress stp offset))
  input : ∀ offset < length, region (byteAddress pointer offset) ∧
    region (panByteAlignHOL (width := 64) (byteAddress pointer offset))
  padding : ∀ offset < 136, region (byteAddress scratch offset) ∧
    region (panByteAlignHOL (width := 64) (byteAddress scratch offset))
  output : ∀ offset < 32, region (byteAddress out offset) ∧
    region (panByteAlignHOL (width := 64) (byteAddress out offset))

theorem block_reads_of_buffers (region : BitVec 64 → Prop) (stp pointer scratch out : BitVec 64)
    (length : Nat) (buffers : BufferRegion region stp pointer scratch out length)
    (index : Nat) (inside : index + 136 ≤ length) :
    KeccakAbsorb.ReadRegion region stp (byteAddress pointer index)
      (KeccakAbsorb.isUnaligned (byteAddress pointer index)) := by
  constructor
  · intro lane
    exact (buffers.state (8 * lane.val) (by have := lane.isLt; omega)).1
  · intro choice lane
    have cell := (buffers.input (index + 8 * lane.val) (by have := lane.isLt; omega)).1
    simpa only [byteAddress, BitVec.ofNat_add, BitVec.add_assoc] using cell
  · intro offset
    have cell := (buffers.input (index + offset.val) (by have := offset.isLt; omega)).2
    simpa only [byteAddress, BitVec.ofNat_add, BitVec.add_assoc] using cell

theorem tail_reads_of_buffers (region : BitVec 64 → Prop) (stp pointer scratch out : BitVec 64)
    (length index : Nat) (ordered : index ≤ length)
    (buffers : BufferRegion region stp pointer scratch out length) :
    TailReads region stp pointer scratch index (length - index) := by
  constructor
  · intro mask offset inside aligned
    have cell := (buffers.input (index + offset) (by omega)).1
    simpa only [byteAddress, BitVec.ofNat_add, BitVec.add_assoc] using cell
  · intro offset inside
    have cell := (buffers.input (index + offset) (by omega)).2
    simpa only [byteAddress, BitVec.ofNat_add, BitVec.add_assoc] using cell
  · exact (buffers.padding 135 (by decide)).2
  · constructor
    · intro lane
      exact (buffers.state (8 * lane.val) (by have := lane.isLt; omega)).1
    · intro choice lane
      exact (buffers.padding (8 * lane.val) (by have := lane.isLt; omega)).1
    · intro offset
      exact (buffers.padding offset.val offset.isLt).2
  · intro offset inside
    exact (buffers.state offset inside).2
  · intro offset inside aligned
    exact (buffers.state offset (by omega)).1
  · intro offset inside
    exact (buffers.state offset (by omega)).2

theorem digest_words_agree (source right : PanSemStateFiniteExact 64 Guest.HostMemory)
    (region : BitVec 64 → Prop) (stp pointer scratch out : BitVec 64) (length : Nat)
    (buffers : BufferRegion region stp pointer scratch out length)
    (same : Agree region source.memory right.memory) :
    MemoryBytes.wordsOf source out = MemoryBytes.wordsOf right out := by
  funext word
  unfold MemoryBytes.wordsOf
  exact congrArg MemoryBytes.wordBits (same _ (buffers.output (8 * word.val) (by have := word.isLt; omega)).1)

/-- Real complete hash calls return identical digest words and FFI event
histories from buffer agreement alone, regardless of private table contents. -/
theorem paired_calls_from_buffers (source right : PanSemStateFiniteExact 64 Guest.HostMemory)
    (sourceArguments rightArguments : List (ExpHOL 64))
    (stp pointer scratch out : BitVec 64) (length : Nat)
    (sourceArgs : evalListHOLFinite source
      (h := fun query => Classical.propDecidable (source.memaddrs query)) sourceArguments = some (values pointer out length))
    (rightArgs : evalListHOLFinite right
      (h := fun query => Classical.propDecidable (right.memaddrs query)) rightArguments = some (values pointer out length))
    (sourceCode : source.code.lookup (ofString "keccak256") = some (formals, body, .one))
    (rightCode : right.code.lookup (ofString "keccak256") = some (formals, body, .one))
    (sourceData : EntryData source stp pointer scratch out length)
    (rightData : EntryData right stp pointer scratch out length)
    (domain : source.memaddrs = right.memaddrs) (endian : source.be = right.be)
    (ffi : source.ffi = right.ffi) (region : BitVec 64 → Prop)
    (buffers : BufferRegion region stp pointer scratch out length)
    (same : Agree region source.memory right.memory) (small : length + 136 < 2^64)
    (sourceClock : price length + 1 ≤ source.clock) (rightClock : price length + 1 ≤ right.clock) :
    ∃ leftOutput rightOutput : PanSemStateFiniteExact 64 Guest.HostMemory,
      evaluateHOLFiniteState source
        (.call (some (none, none)) (ofString "keccak256") sourceArguments) = (none, leftOutput) ∧
      evaluateHOLFiniteState right
        (.call (some (none, none)) (ofString "keccak256") rightArguments) = (none, rightOutput) ∧
      leftOutput.locals = source.locals ∧ rightOutput.locals = right.locals ∧
      leftOutput.ffi = rightOutput.ffi ∧
      MemoryBytes.wordsOf leftOutput out = MemoryBytes.wordsOf rightOutput out ∧
      Agree region leftOutput.memory rightOutput.memory := by
  have div := Nat.mod_add_div length 136
  obtain ⟨leftOutput, rightOutput, leftRun, rightRun, leftLocals, rightLocals,
    leftUpper, leftLower, rightUpper, rightLower, leftControl, rightControl,
    finalFfi, finalMemory, leftAway, rightAway⟩ :=
    paired_call_execute source right sourceArguments rightArguments stp pointer scratch out length
      sourceArgs rightArgs sourceCode rightCode sourceData rightData domain endian ffi region same
      (block_reads_of_buffers region stp pointer scratch out length buffers)
      (by intro offset inside; exact (buffers.state offset inside).2)
      (tail_reads_of_buffers region stp pointer scratch out length (136 * (length / 136)) (by omega) buffers)
      small sourceClock rightClock
  exact ⟨leftOutput, rightOutput, leftRun, rightRun, leftLocals, rightLocals, finalFfi,
    digest_words_agree leftOutput rightOutput region stp pointer scratch out length buffers finalMemory, finalMemory⟩

end InitECandidate.Solver.WitnessRadix.Keccak256

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.block_reads_of_buffers
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.tail_reads_of_buffers
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.digest_words_agree
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.paired_calls_from_buffers
