import InitECandidate.Solver.Input.ScalarProgram

namespace InitECandidate.Solver.Input.Scalar
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

/-- The actual expanded LD_LE64 expression, including its nested high uint32
read, returns the natural eight-byte scalar. -/
theorem le64_read {F : Type} (source : PanSemStateFiniteExact 64 F) (expression : ExpHOL 64) (pointer : BitVec 64) (bytes : Fin 8→UInt8)
    (addressRead : eval source expression=some (.val (.word pointer)))
    (loaded : ∀ index : Fin 8,@panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be
      (pointer+BitVec.ofNat 64 index.val)=some (bytes index)) :
    eval source (le64 expression)=some (.val (.word (BitVec.ofNat 64
      (((bytes 0).toNat+(bytes 1).toNat*256+(bytes 2).toNat*65536+(bytes 3).toNat*16777216)+
       ((bytes 4).toNat+(bytes 5).toNat*256+(bytes 6).toNat*65536+(bytes 7).toNat*16777216)*4294967296)))) := by
  classical
  let highBytes : Fin 4→UInt8:=fun index=>bytes ⟨4+index.val,by have:=index.isLt; omega⟩
  have highRead:=le32_read source (plus expression 4) (pointer+4#64) highBytes
    (plus_read source expression pointer 4 addressRead) (by
      intro index
      have read:=loaded ⟨4+index.val,by have:=index.isLt; omega⟩
      simpa only [BitVec.ofNat_add,BitVec.add_assoc] using read)
  have highExact : eval source (le32 (plus expression 4))=some (.val (.word (BitVec.ofNat 64
      ((bytes 4).toNat+(bytes 5).toNat*256+(bytes 6).toNat*65536+(bytes 7).toNat*16777216)))) := highRead
  have sHigh:=shift_read source _ _ 32 (by decide) highExact
  have b0:=byte_read source expression pointer (bytes 0) addressRead (by simpa using loaded 0)
  have b1:=byte_read source (plus expression 1) _ (bytes 1) (plus_read source expression pointer 1 addressRead) (loaded 1)
  have b2:=byte_read source (plus expression 2) _ (bytes 2) (plus_read source expression pointer 2 addressRead) (loaded 2)
  have b3:=byte_read source (plus expression 3) _ (bytes 3) (plus_read source expression pointer 3 addressRead) (loaded 3)
  have s1:=shift_read source _ _ 8 (by decide) b1
  have s2:=shift_read source _ _ 16 (by decide) b2
  have s3:=shift_read source _ _ 24 (by decide) b3
  simp only [eval] at b0 s1 s2 s3 sHigh ⊢
  rw [le64,evalHOLExact]
  simp only [evalListHOLExact,b0,s1,s2,s3,sHigh,valueIsWord,valueWord,List.all_cons,List.all_nil,
    Bool.and_self,List.map_cons,List.map_nil,wordOpHOL,wordOp,OrOp.or,List.foldr_cons,List.foldr_nil,
    Option.map_some,↓reduceIte,or_zero_raw]
  have assembled:=WordCodec.word8_eq (bytes 0).toNat (bytes 1).toNat (bytes 2).toNat (bytes 3).toNat
    (bytes 4).toNat (bytes 5).toNat (bytes 6).toNat (bytes 7).toNat
    (bytes 0).toNat_lt_size (bytes 1).toNat_lt_size (bytes 2).toNat_lt_size (bytes 3).toNat_lt_size
    (bytes 4).toNat_lt_size (bytes 5).toNat_lt_size (bytes 6).toNat_lt_size (bytes 7).toNat_lt_size
  rw [WordCodec.word8,WordCodec.word4_eq _ _ _ _
    (bytes 4).toNat_lt_size (bytes 5).toNat_lt_size (bytes 6).toNat_lt_size (bytes 7).toNat_lt_size] at assembled
  have lifted:=congrArg (fun value : BitVec 64=>some (ValueHOL.val (HolWordLab.word value))) assembled
  have rawAssoc (a b c : BitVec 64) : BitVec.or (BitVec.or a b) c=BitVec.or a (BitVec.or b c) := BitVec.or_assoc a b c
  simpa only [WordCodec.word4,HOr.hOr,OrOp.or,rawAssoc] using lifted

end InitECandidate.Solver.Input.Scalar

#print axioms InitECandidate.Solver.Input.Scalar.le64_read
