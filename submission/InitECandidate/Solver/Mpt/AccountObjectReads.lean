import InitECandidate.Solver.Mpt.AccountIsEmptyReads

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem Image.scalar_read_at (source : PanSemStateFiniteExact 64 Guest.HostMemory) (account : BitVec 64)
    (image : Image source account) (name : String)
    (binding : source.locals.lookup (ofString name) = some (.val (.word account)))
    (offset : Nat) (inside : offset + 8 ≤ 56) (aligned : offset % 8 = 0) :
    eval source (.load .one (.op .add [localVar name,.const (BitVec.ofNat 64 offset)])) =
      some (.val (.word (MemoryBytes.wordBits (source.memory (account + BitVec.ofNat 64 offset))))) := by
  have mapped : source.memaddrs (account + BitVec.ofNat 64 offset) := by
    rw [image.domain]
    exact image.output.word_mapped account offset inside aligned
  cases cell : source.memory (account + BitVec.ofNat 64 offset) with
  | word word =>
    simp [eval,localVar,evalHOLExact,evalListHOLExact,toExact,binding,valueIsWord,valueWord,wordOpHOL,wordOp,
      memLoadHOLExact,isWfShapeExactHOL,mapped,cell,MemoryBytes.wordBits]

theorem Image.balance_read_at (source : PanSemStateFiniteExact 64 Guest.HostMemory) (account : BitVec 64)
    (image : Image source account) (name : String)
    (binding : source.locals.lookup (ofString name) = some (.val (.word account))) :
    eval source (.load Input.RlpWrite.U256Value.tupleShape (.op .add [localVar name,.const 8#64])) =
      some (Input.RlpWrite.U256Value.tuple (Input.RlpWrite.U256Value.memoryWords source (account + 8#64))) := by
  apply Input.RlpWrite.U256Value.load
  · simp [eval,localVar,evalHOLExact,evalListHOLExact,toExact,binding,valueIsWord,valueWord,wordOpHOL,wordOp]
  · intro index
    rw [image.domain]
    have bound := index.isLt
    simpa [BitVec.ofNat_add,BitVec.add_assoc] using image.output.word_mapped account (8 + 8 * index.val) (by omega) (by omega)

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.Image.scalar_read_at
#print axioms InitECandidate.Solver.Mpt.AccountDecode.Image.balance_read_at
