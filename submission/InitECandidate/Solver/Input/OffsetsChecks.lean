import InitECandidate.Solver.Input.OffsetsStepProgram

namespace InitECandidate.Solver.Input.Offsets
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem range_read {F : Type} (source : PanSemStateFiniteExact 64 F) (current fixed total : BitVec 64)
    (currentLocal : source.locals.lookup (ofString "o")=some (.val (.word current)))
    (fixedLocal : source.locals.lookup (ofString "fixed")=some (.val (.word fixed)))
    (totalLocal : source.locals.lookup (ofString "len")=some (.val (.word total))) :
    eval source rangeTest=some (.val (.word (if current.toNat<fixed.toNat ∨ total.toNat<current.toNat then 1#64 else 0#64))) := by
  classical
  by_cases low : current.toNat<fixed.toNat <;> by_cases high : total.toNat<current.toNat <;>
    simp [eval,rangeTest,localVar,evalHOLExact,evalListHOLExact,toExact,currentLocal,fixedLocal,totalLocal,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,valueIsWord,valueWord,wordOpHOL,wordOp,low,high,OrOp.or]

theorem has_previous_read {F : Type} (source : PanSemStateFiniteExact 64 F) (index : Nat) (small : index≤8)
    (indexLocal : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    eval source hasPrevious=some (.val (.word (if 0<index then 1#64 else 0#64))) := by
  classical
  have encoded : (BitVec.ofNat 64 index).toNat=index := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have sign : index<9223372036854775808 := by omega
  simp [eval,hasPrevious,localVar,evalHOLExact,toExact,indexLocal,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,encoded,sign]

theorem previous_read {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer prior : BitVec 64) (index : Nat)
    (pointerLocal : source.locals.lookup (ofString "offs")=some (.val (.word pointer)))
    (indexLocal : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (mapped : source.memaddrs (pointer+BitVec.ofNat 64 (8*index)-8#64))
    (cell : source.memory (pointer+BitVec.ofNat 64 (8*index)-8#64)=.word prior) :
    eval source previous=some (.val (.word prior)) := by
  classical
  have address:=cell_address_read source pointer index pointerLocal indexLocal
  have subtraction : eval source (.op .sub [cellAddress,.const 8#64])=
      some (.val (.word (pointer+BitVec.ofNat 64 (8*index)-8#64))) := by
    simp only [eval] at address ⊢
    rw [evalHOLExact]
    have constant : @evalHOLExact 64 F _ source.toExact (fun address=>Classical.propDecidable (source.memaddrs address)) (.const 8#64)=some (.val (.word 8#64)) := rfl
    simp [evalListHOLExact,address,constant,valueIsWord,valueWord,wordOpHOL,wordOp]
  simp only [eval] at subtraction ⊢
  rw [previous,evalHOLExact,subtraction]
  simp [memLoadHOLExact,isWfShapeExactHOL,toExact,mapped,cell]

theorem order_read {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer current prior : BitVec 64) (index : Nat)
    (pointerLocal : source.locals.lookup (ofString "offs")=some (.val (.word pointer)))
    (indexLocal : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (currentLocal : source.locals.lookup (ofString "o")=some (.val (.word current)))
    (mapped : source.memaddrs (pointer+BitVec.ofNat 64 (8*index)-8#64))
    (cell : source.memory (pointer+BitVec.ofNat 64 (8*index)-8#64)=.word prior) :
    eval source orderTest=some (.val (.word (if current.toNat<prior.toNat then 1#64 else 0#64))) := by
  classical
  have priorRead:=previous_read source pointer prior index pointerLocal indexLocal mapped cell
  have currentRead : eval source (localVar "o")=some (.val (.word current)) := by
    simpa [eval,localVar,evalHOLExact,toExact] using currentLocal
  simp only [eval] at priorRead currentRead ⊢
  rw [orderTest,evalHOLExact]
  simp [priorRead,currentRead,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]

end InitECandidate.Solver.Input.Offsets

#print axioms InitECandidate.Solver.Input.Offsets.range_read
#print axioms InitECandidate.Solver.Input.Offsets.has_previous_read
#print axioms InitECandidate.Solver.Input.Offsets.previous_read
#print axioms InitECandidate.Solver.Input.Offsets.order_read
