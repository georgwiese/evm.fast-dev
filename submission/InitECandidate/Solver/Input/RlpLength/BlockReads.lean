import InitECandidate.Solver.Input.RlpLength.BlockProgram

namespace InitECandidate.Solver.Input.RlpLength.Block
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index count : Nat)
    (indexSmall : index<2^63) (countSmall : count<2^63)
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (n : source.locals.lookup (ofString "nwd")=some (.val (.word (BitVec.ofNat 64 count)))) :
    eval source loopTest=some (.val (.word (if index<count then 1#64 else 0#64))) := by
  classical
  have indexSign : index<9223372036854775808:=indexSmall
  have countSign : count<9223372036854775808:=countSmall
  have ie : (BitVec.ofNat 64 index).toNat=index := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have ce : (BitVec.ofNat 64 count).toNat=count := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  simp [eval,loopTest,localVar,evalHOLExact,toExact,i,n,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
    Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,BitVec.lt_def,ie,ce,indexSign,countSign]

theorem arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer payload : BitVec 64) (start index : Nat)
    (pl : source.locals.lookup (ofString "pl")=some (.val (.word payload)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (mapped : source.memaddrs (payload+48#64)) (stored : source.memory (payload+48#64)=.word (pointer+BitVec.ofNat 64 start)) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) withdrawalArguments=
      some [.val (.word (pointer+BitVec.ofNat 64 (start+44*index)))] := by
  classical
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,withdrawalArguments,withdrawalBase,localVar,pl,i,mapped,stored,
    memLoadHOLExact,isWfShapeExactHOL,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,BitVec.add_assoc,
    ←BitVec.ofNat_mul,←BitVec.ofNat_add,Nat.mul_comm]

end InitECandidate.Solver.Input.RlpLength.Block

#print axioms InitECandidate.Solver.Input.RlpLength.Block.test_read
#print axioms InitECandidate.Solver.Input.RlpLength.Block.arguments_read
