import InitECandidate.Solver.Input.WordAssemble
import InitECandidate.Solver.Input.HeapInput

namespace InitECandidate.Solver.Input.Scalar
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

def plus (address : ExpHOL 64) (offset : Nat) : ExpHOL 64 := .op .add [address,.const (BitVec.ofNat 64 offset)]
def shift (expression : ExpHOL 64) (bits : Nat) : ExpHOL 64 := .shift .lsl expression (.const (BitVec.ofNat 64 bits))
def le32 (address : ExpHOL 64) : ExpHOL 64 := .op .or [.loadByte address,
  shift (.loadByte (plus address 1)) 8,shift (.loadByte (plus address 2)) 16,shift (.loadByte (plus address 3)) 24]
def le64 (address : ExpHOL 64) : ExpHOL 64 := .op .or [.loadByte address,
  shift (.loadByte (plus address 1)) 8,shift (.loadByte (plus address 2)) 16,shift (.loadByte (plus address 3)) 24,
  shift (le32 (plus address 4)) 32]

theorem or_zero_raw (word : BitVec 64) : BitVec.or word (0 : BitVec 64)=word := BitVec.or_zero

theorem plus_read {F : Type} (source : PanSemStateFiniteExact 64 F) (expression : ExpHOL 64) (pointer : BitVec 64) (offset : Nat)
    (read : eval source expression=some (.val (.word pointer))) :
    eval source (plus expression offset)=some (.val (.word (pointer+BitVec.ofNat 64 offset))) := by
  classical
  simp only [eval] at read ⊢
  rw [plus,evalHOLExact]
  simp [evalListHOLExact,read,evalHOLExact,valueIsWord,valueWord,wordOpHOL,wordOp]

theorem byte_read {F : Type} (source : PanSemStateFiniteExact 64 F) (expression : ExpHOL 64) (pointer : BitVec 64) (byte : UInt8)
    (addressRead : eval source expression=some (.val (.word pointer)))
    (loaded : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be pointer=some byte) :
    eval source (.loadByte expression)=some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
  classical
  simp only [eval] at addressRead ⊢
  rw [evalHOLExact,addressRead]
  simp only [toExact,loaded,Option.map_some]

theorem shift_read {F : Type} (source : PanSemStateFiniteExact 64 F) (expression : ExpHOL 64) (value : BitVec 64) (bits : Nat)
    (small : bits<64) (read : eval source expression=some (.val (.word value))) :
    eval source (shift expression bits)=some (.val (.word (value <<< bits))) := by
  classical
  simp only [eval] at read ⊢
  rw [shift,evalHOLExact]
  have encoded : (BitVec.ofNat 64 bits).toNat=bits := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  simp [read,evalHOLExact,wordShiftHOL,encoded,
    show ¬(bits≠0 ∧ 64≤bits) from by omega]

/-- Exact expanded LD_LE32 expression of the guest, including each actual
byte load and shift; the resulting scalar is a natural uint32 value. -/
theorem le32_read {F : Type} (source : PanSemStateFiniteExact 64 F) (expression : ExpHOL 64) (pointer : BitVec 64) (bytes : Fin 4→UInt8)
    (addressRead : eval source expression=some (.val (.word pointer)))
    (loaded : ∀ index : Fin 4,@panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be
      (pointer+BitVec.ofNat 64 index.val)=some (bytes index)) :
    eval source (le32 expression)=some (.val (.word (BitVec.ofNat 64
      ((bytes 0).toNat+(bytes 1).toNat*256+(bytes 2).toNat*65536+(bytes 3).toNat*16777216)))) := by
  classical
  have b0:=byte_read source expression pointer (bytes 0) addressRead (by simpa using loaded 0)
  have b1:=byte_read source (plus expression 1) _ (bytes 1) (plus_read source expression pointer 1 addressRead) (loaded 1)
  have b2:=byte_read source (plus expression 2) _ (bytes 2) (plus_read source expression pointer 2 addressRead) (loaded 2)
  have b3:=byte_read source (plus expression 3) _ (bytes 3) (plus_read source expression pointer 3 addressRead) (loaded 3)
  have s1:=shift_read source _ _ 8 (by decide) b1
  have s2:=shift_read source _ _ 16 (by decide) b2
  have s3:=shift_read source _ _ 24 (by decide) b3
  simp only [eval] at b0 s1 s2 s3 ⊢
  rw [le32,evalHOLExact]
  simp only [evalListHOLExact,b0,s1,s2,s3,valueIsWord,valueWord,List.all_cons,List.all_nil,
    Bool.and_self,List.map_cons,List.map_nil,wordOpHOL,wordOp,OrOp.or,List.foldr_cons,List.foldr_nil,BitVec.or_zero,
    Option.map_some,↓reduceIte]
  simp only [or_zero_raw]
  simpa only [WordCodec.word4,HOr.hOr,OrOp.or] using congrArg (fun value : BitVec 64=>some (ValueHOL.val (HolWordLab.word value)))
    (WordCodec.word4_eq _ _ _ _ (bytes 0).toNat_lt_size (bytes 1).toNat_lt_size (bytes 2).toNat_lt_size (bytes 3).toNat_lt_size)

end InitECandidate.Solver.Input.Scalar

#print axioms InitECandidate.Solver.Input.Scalar.plus_read
#print axioms InitECandidate.Solver.Input.Scalar.byte_read
#print axioms InitECandidate.Solver.Input.Scalar.shift_read
#print axioms InitECandidate.Solver.Input.Scalar.le32_read

#print axioms InitECandidate.Solver.Input.Scalar.or_zero_raw
