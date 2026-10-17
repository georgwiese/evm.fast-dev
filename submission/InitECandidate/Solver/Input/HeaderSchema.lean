import InitECandidate.Solver.Input.HeaderEntryProgram

namespace InitECandidate.Solver.Input.Header
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem byte_word_equal (input : Guest.InputBlob) (index value : Nat) (small : value<2^64) :
    BitVec.ofNat 64 (Guest.GasLimit.byte input index)=BitVec.ofNat 64 value ↔ Guest.GasLimit.byte input index=value := by
  have byteSmall : Guest.GasLimit.byte input index<2^64 := by
    have bound:=((input[index]?).getD 0).isLt
    change ((input[index]?).getD 0).toNat<2^64
    omega
  constructor
  · intro equal
    have number:=congrArg BitVec.toNat equal
    simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt byteSmall,Nat.mod_eq_of_lt small] using number
  · intro equal
    rw [equal]

theorem schema_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer : BitVec 64)
    (heap : Blob.HeapInput source input pointer) (inside : 2≤input.length%2^64)
    (pointerLocal : source.locals.lookup (ofString "p")=some (.val (.word pointer))) :
    eval source schemaTest=some (.val (.word
      (if Guest.GasLimit.byte input 0≠21 ∨ Guest.GasLimit.byte input 1≠1 then 1#64 else 0#64))) := by
  classical
  have pRead : eval source (localVar "p")=some (.val (.word pointer)) := by
    simpa [eval,localVar,evalHOLExact,toExact] using pointerLocal
  have b0:=Scalar.byte_read source (localVar "p") pointer (Framing.convert ((input[0]?).getD 0)) pRead
    (by simpa using heap 0 (by omega))
  have b1:=Scalar.byte_read source (Scalar.plus (localVar "p") 1) (pointer+1#64) (Framing.convert ((input[1]?).getD 0))
    (Scalar.plus_read source (localVar "p") pointer 1 pRead) (heap 1 (by omega))
  simp only [Scalar.convert_nat] at b0 b1
  change eval source (.loadByte (localVar "p"))=some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.byte input 0)))) at b0
  change eval source (.loadByte (Scalar.plus (localVar "p") 1))=some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.byte input 1)))) at b1
  have equal0:=byte_word_equal input 0 21 (by decide)
  have equal1:=byte_word_equal input 1 1 (by decide)
  have firstRead : eval source schemaFirst=some (.val (.word (if Guest.GasLimit.byte input 0≠21 then 1#64 else 0#64))) := by
    simp only [eval] at b0 ⊢
    rw [schemaFirst,evalHOLExact,b0]
    simp only [evalHOLExact,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,Bool.not_eq_true',beq_eq_false_iff_ne,ne_eq,equal0]
    rfl
  have secondRead : eval source schemaSecond=some (.val (.word (if Guest.GasLimit.byte input 1≠1 then 1#64 else 0#64))) := by
    simp only [eval] at b1 ⊢
    rw [schemaSecond,evalHOLExact,b1]
    simp only [evalHOLExact,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,Bool.not_eq_true',beq_eq_false_iff_ne,ne_eq,equal1]
    rfl
  have orRead : eval source (.op .or [schemaFirst,schemaSecond])=some (.val (.word
      (if Guest.GasLimit.byte input 0≠21 ∨ Guest.GasLimit.byte input 1≠1 then 1#64 else 0#64))) := by
    simp only [eval] at firstRead secondRead ⊢
    rw [evalHOLExact]
    by_cases a : Guest.GasLimit.byte input 0≠21 <;> by_cases b : Guest.GasLimit.byte input 1≠1 <;>
      simp [evalListHOLExact,firstRead,secondRead,a,b,valueIsWord,valueWord,wordOpHOL,wordOp,OrOp.or]
  simp only [eval] at orRead ⊢
  rw [schemaTest,evalHOLExact]
  have zero : @evalHOLExact 64 Guest.HostMemory _ source.toExact (fun address=>Classical.propDecidable (source.memaddrs address)) (.const 0#64)=some (.val (.word 0#64)) := rfl
  by_cases bad : Guest.GasLimit.byte input 0≠21 ∨ Guest.GasLimit.byte input 1≠1 <;>
    simp [zero,orRead,bad,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

end InitECandidate.Solver.Input.Header

#print axioms InitECandidate.Solver.Input.Header.byte_word_equal
#print axioms InitECandidate.Solver.Input.Header.schema_read
