import InitECandidate.Solver.Mpt.AccountDecodeProgram
import InitECandidate.Solver.Rlp.ListItemAt
import InitECandidate.Solver.Input.LoadWordCase

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
attribute [local instance] Classical.propDecidable

/-- Both literal record loads either produce the proven pointer/total or
fail their actual mapping checks before the field decoder is called. -/
theorem field_arguments_cases (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array pointer : BitVec 64)
    (items : List Rlp.ListItem) (index : Nat) (item : Rlp.ListItem)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (records : Rlp.Slices.Records source.memory array pointer items) (selected : items[index]?=some item) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) (fieldArguments index)=
      if source.memaddrs (array+BitVec.ofNat 64 (16*index)) then
        if source.memaddrs (array+BitVec.ofNat 64 (16*index)+8#64) then
          some (Rlp.Header.values (Rlp.Slices.itemPointer pointer items index) item.total) else none
      else none := by
  classical
  obtain ⟨pointerWord,lengthWord⟩ := Rlp.Slices.Records.at source.memory array pointer items records index item selected
  have firstAddress : eval source (.op .add [localVar "arr",.panop .mul [.const (BitVec.ofNat 64 index),.const 16#64]])=
      some (.val (.word (array+BitVec.ofNat 64 (16*index)))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,arrayCell,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,←BitVec.ofNat_mul,Nat.mul_comm]
  have secondAddress : eval source (.op .add [localVar "arr",.panop .mul [.const (BitVec.ofNat 64 index),.const 16#64],.const 8#64])=
      some (.val (.word (array+BitVec.ofNat 64 (16*index)+8#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,arrayCell,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,←BitVec.ofNat_mul,Nat.mul_comm,BitVec.add_assoc]
  have firstRead := Input.load_one_case source _ _ _ firstAddress pointerWord
  have secondRead := Input.load_one_case source _ _ _ secondAddress lengthWord
  simp only [eval] at firstRead secondRead
  simp only [fieldArguments,evalListHOLFinite,evalListHOLExact,firstRead,secondRead]
  by_cases firstMapped : source.memaddrs (array+BitVec.ofNat 64 (16*index))
  all_goals by_cases secondMapped : source.memaddrs (array+BitVec.ofNat 64 (16*index)+8#64)
  all_goals simp [firstMapped,secondMapped,Rlp.Header.values]

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.field_arguments_cases
