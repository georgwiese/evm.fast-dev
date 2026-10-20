import InitECandidate.Solver.Input.MerkleAllocation
import InitECandidate.Solver.Input.BufferCallTrace

namespace InitECandidate.Solver.Input.Merkle
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def bufferCopyArguments : List (ExpHOL 64) := [localVar "buf",localVar "p",.panop .mul [localVar "n",.const 32#64]]
def bufferZeroArguments : List (ExpHOL 64) := [.op .add [localVar "buf",.panop .mul [localVar "n",.const 32#64]],
  .panop .mul [.op .sub [localVar "size",localVar "n"],.const 32#64]]
def afterCopy : ProgHOL 64 := match afterBuffer with | .seq _ rest=>rest | _=>.skip
def afterClear : ProgHOL 64 := match afterCopy with | .seq _ rest=>rest | _=>.skip
def denseContinuation : ProgHOL 64 := match afterClear with | .dec _ _ _ rest=>rest | _=>.skip

set_option maxRecDepth 100000 in
theorem buffer_shape : afterBuffer=.seq (.call (some (none,none)) (ofString "memcpy") bufferCopyArguments) afterCopy ∧
    afterCopy=.seq (.call (some (none,none)) (ofString "memzero") bufferZeroArguments) afterClear ∧
    afterClear=.dec (ofString "cur") .one (localVar "size") denseContinuation := by
  simp only [afterCopy,afterClear,denseContinuation,afterBuffer,afterMark,afterZero,afterDepth,afterCount,afterLimit,body,Guest.guestFn_merkleize,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,bufferCopyArguments,bufferZeroArguments,localVar]
  exact ⟨True.intro,True.intro,True.intro⟩

theorem buffer_copy_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor : BitVec 64) (n : Nat)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (buffer : source.locals.lookup (ofString "buf")=some (.val (.word cursor)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n)))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) bufferCopyArguments=
      some (CopyGeneral.values cursor p (32*n)) := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,bufferCopyArguments,localVar,pointer,buffer,count,
    CopyGeneral.values,valueIsWord,valueWord,panOpHOL,BitVec.ofNat_mul,Nat.mul_comm]

theorem buffer_zero_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) (n size : Nat)
    (inside : n≤size) (small : n<2^64)
    (buffer : source.locals.lookup (ofString "buf")=some (.val (.word cursor)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (sizeLocal : source.locals.lookup (ofString "size")=some (.val (.word (BitVec.ofNat 64 size)))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) bufferZeroArguments=
      some (Zero.values (cursor+BitVec.ofNat 64 (32*n)) (32*(size-n))) := by
  have difference := BitVec.ofNat_sub_ofNat_of_le (w:=64) size n small inside
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,evalHOLExact,toExact,bufferZeroArguments,localVar,buffer,count,sizeLocal,
    Zero.values,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,difference,BitVec.ofNat_mul,Nat.mul_comm]

end InitECandidate.Solver.Input.Merkle

#print axioms InitECandidate.Solver.Input.Merkle.buffer_shape
#print axioms InitECandidate.Solver.Input.Merkle.buffer_copy_arguments
#print axioms InitECandidate.Solver.Input.Merkle.buffer_zero_arguments
