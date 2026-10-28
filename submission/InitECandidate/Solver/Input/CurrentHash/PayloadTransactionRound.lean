import InitECandidate.Solver.Input.CurrentHash.PayloadProgram
import InitECandidate.Solver.Input.CurrentHash.PBytesMemory
import InitECandidate.Solver.Input.CurrentHash.MemoryContextTransport
import InitECandidate.Solver.Input.CounterFlow

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash.Transactions
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Physical decoded rows; the empty list requires no readable array. -/
structure Image (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array : BitVec 64) (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n : Nat) : Prop where
  fields : ∀ index<n,source.memory (array+BitVec.ofNat 64 (16*index))=.word (pointers index) ∧
    source.memory (array+BitVec.ofNat 64 (16*index+8))=.word (BitVec.ofNat 64 (lengths index))

structure RoundState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array roots cursor chunk zeros : BitVec 64)
    (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n index : Nat) : Prop where
  context : MerkleMemory.Context source cursor zeros array
  arrayLocal : source.locals.lookup (ofString "txs")=some (.val (.word array))
  count : source.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 n)))
  rootsLocal : source.locals.lookup (ofString "roots")=some (.val (.word roots))
  position : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))
  image : Image source array pointers lengths n
  chunkCell : source.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk))

/-- Entry geometry only. Actual returning temporary allocations supply their
own room; no maximum temporary arena or later successful call is a premise. -/
structure Geometry (array roots cursor chunk : BitVec 64) (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n capacity : Nat) : Prop where
  countBound : n≤134217728
  capacityBound : capacity≤251655056
  lengthsBound : ∀ index<n,lengths index≤capacity
  arrayArena : 0<n→AllocatedBytes.Arena array (16*n)
  arrayAligned : array.toNat%8=0
  arrayBefore : 0<n→array.toNat+16*n≤roots.toNat
  chunkBefore : 0<n→chunk.toNat+32≤array.toNat
  chunkArena : AllocatedBytes.Arena chunk 32
  chunkAligned : chunk.toNat%8=0
  rootsArena : AllocatedBytes.Arena roots (32*n)
  rootsAligned : roots.toNat%8=0
  rootsBefore : roots.toNat+32*n≤cursor.toNat
  inputs : ∀ index<n,AllocatedBytes.Arena (pointers index) (lengths index)

theorem RoundState.dec_clock {source : PanSemStateFiniteExact 64 Guest.HostMemory} {array roots cursor chunk zeros : BitVec 64}
    {pointers : Nat→BitVec 64} {lengths : Nat→Nat} {n index : Nat}
    (data : RoundState source array roots cursor chunk zeros pointers lengths n index) :
    RoundState (decClockHOLFinite source) array roots cursor chunk zeros pointers lengths n index :=
  ⟨data.context.of_frozen rfl,data.arrayLocal,data.count,data.rootsLocal,data.position,⟨data.image.fields⟩,data.chunkCell⟩

theorem arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array roots cursor chunk zeros : BitVec 64) (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n capacity index : Nat)
    (actual : RoundState source array roots cursor chunk zeros pointers lengths n index)
    (geometry : Geometry array roots cursor chunk pointers lengths n capacity) (active : index<n) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) transactionArguments=
      some (CallNormal.tripleValues (pointers index) (BitVec.ofNat 64 (lengths index)) (roots+BitVec.ofNat 64 (32*index))) := by
  have arena := geometry.arrayArena (by omega)
  have pMapped : source.memaddrs (array+BitVec.ofNat 64 (16*index)) :=
    AllocatedBytes.word_mapped source array (16*n) (16*index) actual.context.domain arena (by omega) geometry.arrayAligned (by omega)
  have nMapped : source.memaddrs (array+BitVec.ofNat 64 (16*index+8)) :=
    AllocatedBytes.word_mapped source array (16*n) (16*index+8) actual.context.domain arena (by omega) geometry.arrayAligned (by omega)
  have product : BitVec.ofNat 64 index*16#64=BitVec.ofNat 64 (16*index) := by
    rw [←BitVec.ofNat_mul,Nat.mul_comm]
  have pRead : eval source (.load .one (.op .add [localVar "txs",.panop .mul [localVar "i",.const 16#64]]))=some (.val (.word (pointers index))) := by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,actual.arrayLocal,actual.position,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,
      product,isWfShapeExactHOL,memLoadHOLExact,pMapped,(actual.image.fields index active).1]
  have nRead : eval source (.load .one (.op .add [localVar "txs",.panop .mul [localVar "i",.const 16#64],.const 8#64]))=some (.val (.word (BitVec.ofNat 64 (lengths index)))) := by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,actual.arrayLocal,actual.position,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,
      product,←BitVec.ofNat_add,isWfShapeExactHOL,memLoadHOLExact,nMapped,(actual.image.fields index active).2]
  have outRead : eval source (.op .add [localVar "roots",.panop .mul [localVar "i",.const 32#64]])=some (.val (.word (roots+BitVec.ofNat 64 (32*index)))) := by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,actual.rootsLocal,actual.position,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,BitVec.ofNat_mul,Nat.mul_comm]
  simp only [eval] at pRead nRead outRead
  simp only [evalListHOLFinite,transactionArguments,evalListHOLExact,pRead,nRead,outRead,CallNormal.tripleValues]

end InitECandidate.Solver.Input.CurrentHash.PayloadHash.Transactions

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Transactions.RoundState.dec_clock
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.Transactions.arguments_read
