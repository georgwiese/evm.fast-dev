import InitECandidate.Solver.Input.WordArrayRead
import InitECandidate.Solver.WitnessRadix.ByteArrayFrame
import Flapjack.Pancake.Semantics.PanProps.MemByteArray
import Flapjack.Pancake.Semantics.PanSem.ExtCallExact

namespace InitECandidate.Solver.Input.WordArrayWriteFrame
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- The trusted UInt8 reader/writer roundtrip transported to the exact
word8 lists used by the real source foreign-call semantics. -/
theorem read_write (memory : BitVec 64 → HolWordLab 64) (domain : BitVec 64 → Prop) (endian : Bool)
    (pointer : BitVec 64) (length : Nat) (bytes : List (BitVec 8))
    (read : readBytearrayWordHOL pointer length
      (@panMemLoadByteWord8HOL 64 _ memory domain (fun query => Classical.propDecidable (domain query)) endian) = some bytes) :
    @panWriteBytearrayWord8HOL 64 _ pointer bytes memory domain (fun query => Classical.propDecidable (domain query)) endian = memory := by
  classical
  have projected := @panReadBytearrayHOL_eq_word8_projection 64 _ pointer length memory domain (fun query => Classical.propDecidable (domain query)) endian
  rw [read] at projected
  have identity := @readWriteBytearrayLemma 64 _ length pointer (bytes.map UInt8.ofBitVec) memory domain
    (fun query => Classical.propDecidable (domain query)) endian ⟨Or.inr rfl,projected⟩
  rw [panWriteBytearrayHOL_eq_word8_projection] at identity
  simpa only [List.map_map,Function.comp_def,UInt8.toBitVec_ofBitVec,List.map_id'] using identity

/-- A real reply may alter other words arbitrarily. A selected word survives
when every reply byte targeting it equals that byte of the actual old memory.
Failed stores and wrapping addresses retain their original semantics. -/
theorem same_word {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer query : BitVec 64) (bytes : List (BitVec 8))
    (same : ∀ offset, (inside : offset < bytes.length) → panByteAlignHOL (width := 64) (byteAddress pointer offset) = query →
      @panMemLoadByteWord8HOL 64 _ source.memory source.memaddrs (fun address => Classical.propDecidable (source.memaddrs address)) source.be
        (byteAddress pointer offset) = some (bytes[offset])) :
    (@panWriteBytearrayWord8HOL 64 _ pointer bytes source.memory source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) source.be) query = source.memory query := by
  classical
  induction bytes generalizing pointer with
  | nil => rfl
  | cons byte rest ih =>
    have tailEq := ih (pointer + 1#64) (by
      intro offset inside hit
      have point : byteAddress (pointer + 1#64) offset = byteAddress pointer (offset + 1) := by
        simp only [byteAddress,BitVec.ofNat_add,BitVec.add_assoc]
        rw [BitVec.add_comm (1#64 : BitVec 64) (BitVec.ofNat 64 offset)]
      have current := same (offset + 1) (by simp only [List.length_cons]; omega) (by rw [← point]; exact hit)
      simpa only [List.getElem_cons_succ,← point] using current)
    let tailMemory := @panWriteBytearrayWord8HOL 64 _ (pointer + 1#64) rest source.memory source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) source.be
    have headEq : (@panWriteBytearrayWord8HOL 64 _ pointer [byte] tailMemory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be) query = tailMemory query := by
      by_cases hit : panByteAlignHOL (width := 64) pointer = query
      · have point : byteAddress pointer 0 = pointer := by simp [byteAddress]
        have oldRead := same 0 (by simp) (by simpa only [point] using hit)
        rw [point] at oldRead
        have oldByte : @panMemLoadByteWord8HOL 64 _ source.memory source.memaddrs
            (fun address => Classical.propDecidable (source.memaddrs address)) source.be pointer = some byte := oldRead
        have cellEq : tailMemory (panByteAlignHOL (width := 64) pointer) = source.memory (panByteAlignHOL (width := 64) pointer) := by
          rw [hit]
          exact tailEq
        have currentRead : @panMemLoadByteWord8HOL 64 _ tailMemory source.memaddrs
            (fun address => Classical.propDecidable (source.memaddrs address)) source.be pointer = some byte := by
          simpa only [panMemLoadByteWord8HOL,cellEq] using oldByte
        have arrayRead : readBytearrayWordHOL pointer 1
            (@panMemLoadByteWord8HOL 64 _ tailMemory source.memaddrs (fun address => Classical.propDecidable (source.memaddrs address)) source.be) = some [byte] := by
          simp [readBytearrayWordHOL,currentRead]
        exact congrArg (fun memory : BitVec 64 → HolWordLab 64 => memory query) (read_write tailMemory source.memaddrs source.be pointer 1 [byte] arrayRead)
      · exact ByteArray.write_away {source with memory := tailMemory} pointer query [byte] (by
          intro offset inside
          have zero : offset = 0 := by simp only [List.length_cons,List.length_nil] at inside; omega
          subst offset
          simpa [byteAddress] using Ne.symm hit)
    rw [panWriteBytearrayWord8HOL]
    have one : (1 : BitVec 64) = 1#64 := rfl
    simp only [one]
    cases stored : @panMemStoreByteWord8HOL 64 _
        (@panWriteBytearrayWord8HOL 64 _ (pointer + 1#64) rest source.memory source.memaddrs
          (fun address => Classical.propDecidable (source.memaddrs address)) source.be)
        source.memaddrs (fun address => Classical.propDecidable (source.memaddrs address)) source.be pointer byte with
    | none => simp only [stored]
    | some updated =>
      have kept : updated query = tailMemory query := by
        simpa only [panWriteBytearrayWord8HOL,tailMemory,stored] using headEq
      simpa only [stored] using kept.trans tailEq

end InitECandidate.Solver.Input.WordArrayWriteFrame

#print axioms InitECandidate.Solver.Input.WordArrayWriteFrame.read_write
#print axioms InitECandidate.Solver.Input.WordArrayWriteFrame.same_word
