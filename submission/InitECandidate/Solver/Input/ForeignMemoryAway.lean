import InitECandidate.Solver.WitnessRadix.ByteArrayFrame
import InitECandidate.Solver.Input.EvaluationFields

namespace InitECandidate.Solver.Input.MemoryAt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix WitnessRadix.QueryBranch

/-- The actual external-call reply writes only the declared byte array.
The evaluator enforces reply length, so this frame needs no oracle contents
or cryptographic assumption and covers final FFI/failure outcomes as well. -/
theorem foreign_current {F : Type} (source : PanSemStateFiniteExact 64 F) (function : MlS)
    (configuration array : ExpHOL 64) (configurationPointer arrayPointer query : BitVec 64) (length : Nat)
    (small : length<2^64)
    (configurationRead : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) configuration=some (.val (.word configurationPointer)))
    (arrayRead : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) array=some (.val (.word arrayPointer)))
    (away : ∀ offset<length,query≠panByteAlignHOL (width:=64) (byteAddress arrayPointer offset)) :
    (evaluateHOLFiniteState source (.extCall function configuration (.const 0#64) array (.const (BitVec.ofNat 64 length)))).2.memory query=source.memory query := by
  have number : (BitVec.ofNat 64 length).toNat=length := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  rw [evaluateHOLFiniteState_extCall_source,configurationRead,arrayRead]
  simp only [evalHOLFinite,evalHOLExact,BitVec.toNat_ofNat,Nat.zero_mod]
  rw [Nat.mod_eq_of_lt small]
  simp only [readBytearrayWordHOL]
  generalize read : readBytearrayWordHOL (byteWidth:=8) arrayPointer length
    (@panMemLoadByteWord8HOL 64 _ source.memory source.memaddrs (fun address=>Classical.propDecidable (source.memaddrs address)) source.be)=bytes
  cases bytes with
  | none=>rfl
  | some bytes=>
    dsimp only
    have originalLength := readBytearrayWordHOL_length _ _ _ _ read
    generalize called : callFFIHOL source.ffi (.extCall function) [] bytes=reply
    cases reply with
    | final event=>rfl
    | ret nextFfi answer=>
      have replyLength := callFFIHOL_ret_length source.ffi (.extCall function) [] bytes answer nextFfi called
      change (@panWriteBytearrayWord8HOL 64 _ arrayPointer answer source.memory source.memaddrs
        (fun address=>Classical.propDecidable (source.memaddrs address)) source.be) query=source.memory query
      exact ByteArray.write_away source arrayPointer query answer (by intro offset inside; exact away offset (by rw [replyLength,originalLength] at inside; exact inside))

end InitECandidate.Solver.Input.MemoryAt

#print axioms InitECandidate.Solver.Input.MemoryAt.foreign_current
