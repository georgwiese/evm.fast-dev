import InitECandidate.Solver.Input.CopyLoopReached
import InitECandidate.Solver.Input.CopyMemory
import InitECandidate.Solver.Input.CopyWalk
import InitECandidate.Solver.Input.HostReadCurrent
import InitECandidate.Solver.Input.ByteDecode

namespace InitECandidate.Solver.Input.Blob
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Byte contents over the actual encoded extent, without restricting the
length of the mathematical input list. -/
def InputBytes (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (input : Guest.InputBlob) (pointer : BitVec 64) (length : Nat) : Prop :=
  ∀ offset < length, @panMemLoadByteHOL 64 _ state.memory state.memaddrs
    (fun address => Classical.propDecidable (state.memaddrs address)) state.be
    (pointer + BitVec.ofNat 64 offset) = some (Framing.convert ((input[offset]?).getD 0))

theorem observed_walk_bytes (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (input : Guest.InputBlob) (pointer : BitVec 64) (length offset : Nat)
    (bounded : length ≤ Guest.maxInputBytes) (inside : offset < length)
    (fits : pointer.toNat + length + 8 < 2^64)
    (aligned : pointer.toNat % 8 = 0) (little : source.be = false)
    (host : source.ffi.ffiState = Guest.guestHostMemory input)
    (observed : ObservedWords source pointer 0 (copyRounds length)) :
    @panMemLoadByteHOL 64 _ (walk source pointer 0 (copyRounds length)).memory source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) source.be
      (pointer + BitVec.ofNat 64 offset) = some (Framing.convert ((input[offset]?).getD 0)) := by
  have fit := copyRounds_fit length bounded
  have wordInside : offset / 8 < copyRounds length := by omega
  have startInside : 8 * (offset / 8) < length := by omega
  have visible : 8 * (offset / 8) + 8 ≤ Guest.maxInputBytes := by
    change length ≤ 1073741808 at bounded
    change 8 * (offset / 8) + 8 ≤ 1073741808
    omega
  obtain ⟨mapped, present⟩ := observed (offset / 8) wordInside
  simp only [Nat.zero_add] at mapped present
  have cell := walk_cell source pointer 0 (copyRounds length) (offset / 8) wordInside (by omega)
  simp only [Nat.zero_add] at cell
  rw [host] at cell present
  rw [CurrentHostRead.present_bytes input _ visible present] at cell
  have addressNat := WitnessRadix.MemoryBytes.offset_toNat pointer offset (by omega)
  have wordNat := WitnessRadix.MemoryBytes.offset_toNat pointer (8 * (offset / 8)) (by omega)
  have alignment : panByteAlignHOL (width := 64) (pointer + BitVec.ofNat 64 offset) =
      pointer + BitVec.ofNat 64 (8 * (offset / 8)) := by
    apply BitVec.eq_of_toNat_eq
    change (BitVec.ofNat 64 (((pointer + BitVec.ofNat 64 offset).toNat / 8) * 8)).toNat = _
    rw [BitVec.toNat_ofNat, addressNat, wordNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have digit : (pointer + BitVec.ofNat 64 offset).toNat % 8 = offset % 8 := by
    rw [addressNat]
    omega
  have decode := WordCodec.decoded_byte (CurrentHostRead.dataBytes input (8 * (offset / 8)))
    (by simp [CurrentHostRead.dataBytes]) (offset % 8) (by omega)
  have byteAt : ((CurrentHostRead.dataBytes input (8 * (offset / 8)))[offset % 8]?).getD 0 =
      Framing.convert ((input[offset]?).getD 0) := by
    rw [List.getElem?_eq_getElem (by simp [CurrentHostRead.dataBytes]; omega)]
    simp only [CurrentHostRead.dataBytes, List.getElem_map, List.getElem_range]
    rw [show 8 * (offset / 8) + offset % 8 = offset from by omega]
    rfl
  have modByte (number : Nat) : UInt8.ofNat (number % 256) = UInt8.ofNat number := by
    apply UInt8.toNat.inj
    simp [UInt8.toNat_ofNat']
  simp only [panMemLoadByteHOL, alignment, mapped, ↓reduceIte, cell, little, panGetByteHOL]
  change some (UInt8.ofNat (((Guest.wordOfLeBytes (CurrentHostRead.dataBytes input (8 * (offset / 8)))).toNat /
    256 ^ ((pointer + BitVec.ofNat 64 offset).toNat % 8)) % 256)) = _
  rw [digit, modByte, decode, byteAt]

/-- Actual normal completion of the unchanged copy loop yields the decoder's
byte view and an exact write-only-to-copied-words frame. No host presence,
destination mapping or successful future access is an entry premise. -/
theorem copy_bytes_reached (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (input : Guest.InputBlob) (pointer old : BitVec 64) (length : Nat)
    (bounded : length ≤ Guest.maxInputBytes) (fits : pointer.toNat + length + 8 < 2^64)
    (aligned : pointer.toNat % 8 = 0) (little : source.be = false)
    (pointerLocal : source.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word 0#64)))
    (lengthLocal : source.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 length))))
    (wordLocal : source.locals.lookup (ofString "w") = some (.val (.word old)))
    (oracleEq : source.ffi.oracle = InitE.sourceOracle)
    (host : source.ffi.ffiState = Guest.guestHostMemory input)
    (normal : evaluateHOLFiniteState source copyLoop = (none, target)) :
    InputBytes target input pointer length ∧
    target.clock = source.clock - copyRounds length ∧
    target.globals = source.globals ∧ target.code = source.code ∧
    target.memaddrs = source.memaddrs ∧ target.shMemaddrs = source.shMemaddrs ∧
    target.ffi.ffiState = source.ffi.ffiState ∧ target.ffi.oracle = source.ffi.oracle ∧
    ∀ query, (∀ slot < copyRounds length, query ≠ pointer + BitVec.ofNat 64 (8 * slot)) →
      target.memory query = source.memory query := by
  have fit := copyRounds_fit length bounded
  obtain ⟨same, observed⟩ := copy_loop_reached source target pointer old 0 length (copyRounds length)
    (by omega) (by omega) (by omega) pointerLocal indexLocal lengthLocal wordLocal oracleEq normal
  rw [same]
  have frame := walk_frame source pointer 0 (copyRounds length)
  refine ⟨?_, walk_clock source pointer 0 (copyRounds length), frame.1, frame.2.1,
    frame.2.2.1, frame.2.2.2.1, frame.2.2.2.2.1, frame.2.2.2.2.2, ?_⟩
  · intro offset inside
    rw [frame.2.2.1, walk_endian]
    exact observed_walk_bytes source input pointer length offset bounded inside fits aligned little host observed
  · intro query away
    apply walk_away
    simpa only [Nat.zero_add] using away

end InitECandidate.Solver.Input.Blob

#print axioms InitECandidate.Solver.Input.Blob.observed_walk_bytes
#print axioms InitECandidate.Solver.Input.Blob.copy_bytes_reached
