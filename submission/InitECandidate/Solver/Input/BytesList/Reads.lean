import InitECandidate.Solver.Input.BytesList.Program

namespace InitECandidate.Solver.Input.BytesList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem loop_test (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array : BitVec 64) (index count : Nat)
    (indexSmall : index<2^63) (countSmall : count<2^63)
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (r : source.locals.lookup (ofString "r")=some (pairValue array count)) :
    eval source loopTest=some (.val (.word (if index<count then 1#64 else 0#64))) := by
  classical
  have indexSign : index<9223372036854775808:=indexSmall
  have countSign : count<9223372036854775808:=countSmall
  have ie : (BitVec.ofNat 64 index).toNat=index := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have ce : (BitVec.ofNat 64 count).toNat=count := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  simp [eval,loopTest,resultCount,pairValue,VarList.pairValue,localVar,evalHOLExact,toExact,i,r,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL,Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,BitVec.lt_def,ie,ce,indexSign,countSign]

theorem length_test (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array maximum value : BitVec 64) (index count : Nat)
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (r : source.locals.lookup (ofString "r")=some (pairValue array count))
    (m : source.locals.lookup (ofString "maxb")=some (.val (.word maximum)))
    (mapped : source.memaddrs (cell array index)) (stored : source.memory (cell array index)=.word value) :
    eval source lengthTest=some (.val (.word (if maximum.toNat<value.toNat then 1#64 else 0#64))) := by
  classical
  have mapped' : source.memaddrs (array+(BitVec.ofNat 64 (index*16)+8#64)) := by simpa only [cell,Nat.mul_comm,BitVec.add_assoc] using mapped
  have stored' : source.memory (array+(BitVec.ofNat 64 (index*16)+8#64))=.word value := by simpa only [cell,Nat.mul_comm,BitVec.add_assoc] using stored
  simp [eval,lengthTest,lengthExpression,lengthAddress,resultPointer,pairValue,VarList.pairValue,localVar,evalHOLExact,evalListHOLExact,toExact,i,r,m,
    cell,←BitVec.ofNat_mul,Nat.mul_comm,BitVec.add_assoc,mapped',stored',memLoadHOLExact,isWfShapeExactHOL,valueIsWord,valueWord,
    panOpHOL,wordOpHOL,wordOp,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]

end InitECandidate.Solver.Input.BytesList

#print axioms InitECandidate.Solver.Input.BytesList.loop_test
#print axioms InitECandidate.Solver.Input.BytesList.length_test
