import InitECandidate.Solver.Mpt.KeyToNibblesScalar

namespace InitECandidate.Solver.Mpt.KeyToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def firstAddress (out index : BitVec 64) (offset : Nat) : BitVec 64 := out + 2#64 * index + BitVec.ofNat 64 (2 * offset)
def secondAddress (out index : BitVec 64) (offset : Nat) : BitVec 64 := out + 2#64 * index + BitVec.ofNat 64 (2 * offset + 1)
def pairState {F : Type} (source : PanSemStateFiniteExact 64 F) (out index : BitVec 64) (offset : Nat) (byte : BitVec 8) : PanSemStateFiniteExact 64 F :=
  {source with memory := (ByteStore.put (ByteStore.put source.memory source.be (firstAddress out index offset) (high byte)) source.be (secondAddress out index offset) (low byte))}

/-- The actual two literal stores, with both nibbles computed from the real
bound byte local. This equality exposes its continuation without assuming
any later successful execution. -/
theorem pair_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (name : String) (offset : Nat)
    (out index : BitVec 64) (byte : BitVec 8) (rest : ProgHOL 64)
    (outCell : source.locals.lookup (ofString "out") = some (.val (.word out)))
    (indexCell : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (byteCell : source.locals.lookup (ofString name) = some (.val (.word (BitVec.ofNat 64 byte.toNat))))
    (firstMapped : source.memaddrs (panByteAlignHOL (width := 64) (firstAddress out index offset)))
    (secondMapped : source.memaddrs (panByteAlignHOL (width := 64) (secondAddress out index offset))) :
    evaluateHOLFiniteState source (pair name offset rest) = evaluateHOLFiniteState (pairState source out index offset byte) rest := by
  have firstRun := ByteStore.execute source (outputAddress (2 * offset)) _ (firstAddress out index offset) (high byte)
    (output_read source out index (2 * offset) outCell indexCell) (high_read source name byte byteCell) firstMapped
  let entered := {source with memory := ByteStore.put source.memory source.be (firstAddress out index offset) (high byte)}
  have secondRun := ByteStore.execute entered (outputAddress (2 * offset + 1)) _ (secondAddress out index offset) (low byte)
    (output_read entered out index (2 * offset + 1) outCell indexCell) (low_read entered name byte byteCell) secondMapped
  rw [pair, evaluateHOLFiniteState_seq_line780, firstRun]
  change evaluateHOLFiniteState entered (.seq _ rest) = _
  rw [evaluateHOLFiniteState_seq_line780, secondRun]
  rfl

theorem addresses_different (out index : BitVec 64) (offset : Nat) :
    firstAddress out index offset ≠ secondAddress out index offset := by
  have step : secondAddress out index offset = firstAddress out index offset + 1#64 := by
    simp only [firstAddress, secondAddress, BitVec.ofNat_add, BitVec.add_assoc]
  intro same
  rw [step] at same
  have number := congrArg BitVec.toNat same
  rw [BitVec.toNat_add] at number
  change (firstAddress out index offset).toNat = ((firstAddress out index offset).toNat + 1) % 2^64 at number
  have small := (firstAddress out index offset).isLt
  omega

theorem pair_reads {F : Type} (source : PanSemStateFiniteExact 64 F) (out index : BitVec 64) (offset : Nat) (byte : BitVec 8)
    (little : source.be = false)
    (firstMapped : source.memaddrs (panByteAlignHOL (width := 64) (firstAddress out index offset)))
    (secondMapped : source.memaddrs (panByteAlignHOL (width := 64) (secondAddress out index offset))) :
    @panMemLoadByteHOL 64 _ (pairState source out index offset byte).memory source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) false (firstAddress out index offset) = some (UInt8.ofNat (high byte).toNat) ∧
    @panMemLoadByteHOL 64 _ (pairState source out index offset byte).memory source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) false (secondAddress out index offset) = some (UInt8.ofNat (low byte).toNat) := by
  change (let memory := (ByteStore.put (ByteStore.put source.memory source.be (firstAddress out index offset) (high byte)) source.be (secondAddress out index offset) (low byte))
    @panMemLoadByteHOL 64 _ memory source.memaddrs (fun address => Classical.propDecidable (source.memaddrs address)) false (firstAddress out index offset) = _ ∧
    @panMemLoadByteHOL 64 _ memory source.memaddrs (fun address => Classical.propDecidable (source.memaddrs address)) false (secondAddress out index offset) = _)
  simp only [little]
  constructor
  · rw [ByteStore.read_other _ source.memaddrs _ _ _ (Ne.symm (addresses_different out index offset))]
    exact ByteStore.read_self source.memory source.memaddrs _ (high byte) firstMapped
  · exact ByteStore.read_self _ source.memaddrs _ (low byte) secondMapped

end InitECandidate.Solver.Mpt.KeyToNibbles

#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.pair_execute
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.addresses_different
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.pair_reads
