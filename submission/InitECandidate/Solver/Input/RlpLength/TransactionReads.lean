import InitECandidate.Solver.Input.RlpLength.TransactionAfterFirst
import InitECandidate.Solver.Input.ScalarProgram
import InitECandidate.Solver.Input.VarList.RecordSizes

namespace InitECandidate.Solver.Input.RlpLength.Block
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem tx_length_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array n : BitVec 64) (index : Nat)
    (txs : source.locals.lookup (ofString "txs")=some (.val (.word array)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (mapped : source.memaddrs (VarList.lengthCell array index)) (stored : source.memory (VarList.lengthCell array index)=.word n) :
    eval source txLengthExpression=some (.val (.word n)) := by
  classical
  have m : source.memaddrs (array+(BitVec.ofNat 64 (index*16)+8#64)) := by simpa only [VarList.lengthCell,VarList.row,Nat.mul_comm,BitVec.add_assoc] using mapped
  have s : source.memory (array+(BitVec.ofNat 64 (index*16)+8#64))=.word n := by simpa only [VarList.lengthCell,VarList.row,Nat.mul_comm,BitVec.add_assoc] using stored
  simp [eval,txLengthExpression,localVar,evalHOLExact,evalListHOLExact,toExact,txs,i,←BitVec.ofNat_mul,BitVec.add_assoc,m,s,
    memLoadHOLExact,isWfShapeExactHOL,valueIsWord,valueWord,panOpHOL,wordOpHOL,wordOp]

theorem tx_first_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array pointer : BitVec 64) (index : Nat) (byte : UInt8)
    (txs : source.locals.lookup (ofString "txs")=some (.val (.word array)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (mapped : source.memaddrs (VarList.row array index)) (stored : source.memory (VarList.row array index)=.word pointer)
    (loaded : @panMemLoadByteHOL 64 _ source.memory source.memaddrs (fun address=>Classical.propDecidable (source.memaddrs address)) source.be pointer=some byte) :
    eval source txFirstExpression=some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
  classical
  have m : source.memaddrs (array+BitVec.ofNat 64 (index*16)) := by simpa only [VarList.row,Nat.mul_comm] using mapped
  have s : source.memory (array+BitVec.ofNat 64 (index*16))=.word pointer := by simpa only [VarList.row,Nat.mul_comm] using stored
  have addressRead : eval source (.load .one txAddress)=some (.val (.word pointer)) := by
    simp [eval,txAddress,localVar,evalHOLExact,evalListHOLExact,toExact,txs,i,←BitVec.ofNat_mul,m,s,
      memLoadHOLExact,isWfShapeExactHOL,valueIsWord,valueWord,panOpHOL,wordOpHOL,wordOp]
  exact Scalar.byte_read source (.load .one txAddress) pointer byte addressRead loaded

theorem tx_step_restore (saved source : PanSemStateFiniteExact 64 Guest.HostMemory) (scope : String) (paid index sum encoded : Nat)
    (tlNe : ofString scope≠ofString "tl") (iNe : ofString scope≠ofString "i") :
    restore saved scope (txStep source paid index sum encoded)=txStep (restore saved scope source) paid index sum encoded := by
  rw [txStep,restore_bind_other saved _ scope "i" _ iNe,restore_bind_other saved _ scope "tl" _ tlNe]
  rfl

end InitECandidate.Solver.Input.RlpLength.Block

#print axioms InitECandidate.Solver.Input.RlpLength.Block.tx_length_read
#print axioms InitECandidate.Solver.Input.RlpLength.Block.tx_first_read
#print axioms InitECandidate.Solver.Input.RlpLength.Block.tx_step_restore
