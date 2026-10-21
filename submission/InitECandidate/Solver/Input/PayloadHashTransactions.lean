import InitECandidate.Solver.Input.PayloadHashProgram
import InitECandidate.Solver.Input.CounterFlow

namespace InitECandidate.Solver.Input.PayloadHash.Transactions
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Actual decoded transaction rows. Empty arrays need no readable pointer. -/
structure Image (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array : BitVec 64) (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n : Nat) : Prop where
  fields : ∀ index<n,source.memory (array+BitVec.ofNat 64 (16*index))=.word (pointers index) ∧
    source.memory (array+BitVec.ofNat 64 (16*index+8))=.word (BitVec.ofNat 64 (lengths index))

structure RoundState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array roots cursor stp accel chunk zeros : BitVec 64)
    (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n index : Nat) : Prop where
  workspace : SszHash.Workspace source stp accel chunk zeros
  arrayLocal : source.locals.lookup (ofString "txs")=some (.val (.word array))
  count : source.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 n)))
  rootsLocal : source.locals.lookup (ofString "roots")=some (.val (.word roots))
  position : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))
  image : Image source array pointers lengths n
  heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor))

/-- Current physical transaction rows, output slots and shared temporary
arena. The empty case has no array mapping/separation obligation. -/
structure Geometry (array roots cursor stp accel chunk : BitVec 64) (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n capacity : Nat) : Prop where
  countBound : n≤134217728
  capacityBound : capacity≤134217728
  lengthsBound : ∀ index<n,lengths index≤capacity
  arrayArena : 0<n→AllocatedBytes.Arena array (16*n)
  arrayAligned : array.toNat%8=0
  arrayBefore : 0<n→array.toNat+16*n≤roots.toNat
  stateBefore : 0<n→stp.toNat+64≤array.toNat
  accelBefore : 0<n→accel.toNat+96≤array.toNat
  chunkBefore : 0<n→chunk.toNat+32≤array.toNat
  rootsArena : AllocatedBytes.Arena roots (32*n)
  rootsAligned : roots.toNat%8=0
  rootsBefore : roots.toNat+32*n≤cursor.toNat
  temporaryArena : AllocatedBytes.Arena cursor (832+96*PackBytes.chunks capacity)
  aligned : cursor.toNat%8=0
  inputs : ∀ index<n,AllocatedBytes.Arena (pointers index) (lengths index)

theorem RoundState.dec_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array roots cursor stp accel chunk zeros : BitVec 64)
    (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n index : Nat)
    (actual : RoundState source array roots cursor stp accel chunk zeros pointers lengths n index) :
    RoundState (decClockHOLFinite source) array roots cursor stp accel chunk zeros pointers lengths n index :=
  ⟨SszHash.Workspace.of_fields source _ stp accel chunk zeros actual.workspace rfl rfl (by intro key different; rfl),actual.arrayLocal,actual.count,actual.rootsLocal,actual.position,⟨actual.image.fields⟩,actual.heap⟩

theorem call_geometry (array roots cursor stp accel chunk : BitVec 64) (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n capacity index : Nat)
    (geometry : Geometry array roots cursor stp accel chunk pointers lengths n capacity) (active : index<n) :
    AllocatedBytes.Arena (roots+BitVec.ofNat 64 (32*index)) 32 ∧
    AllocatedBytes.Arena cursor (832+96*PackBytes.chunks (lengths index)) := by
  have lengthBound := geometry.lengthsBound index active
  have chunksBound : PackBytes.chunks (lengths index)≤PackBytes.chunks capacity := by unfold PackBytes.chunks; omega
  exact ⟨AllocatedBytes.Arena.subrange roots (32*n) (32*index) 32 geometry.rootsArena (by omega),
    AllocatedBytes.Arena.weaken cursor (832+96*PackBytes.chunks capacity) _ geometry.temporaryArena (by omega)⟩

theorem arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array roots cursor stp accel chunk zeros : BitVec 64) (pointers : Nat→BitVec 64) (lengths : Nat→Nat) (n capacity index : Nat)
    (actual : RoundState source array roots cursor stp accel chunk zeros pointers lengths n index)
    (geometry : Geometry array roots cursor stp accel chunk pointers lengths n capacity) (active : index<n) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) transactionArguments=
      some (PBytes.values (pointers index) (lengths index) (roots+BitVec.ofNat 64 (32*index))) := by
  have arena := geometry.arrayArena (by omega)
  have pMapped : source.memaddrs (array+BitVec.ofNat 64 (16*index)) :=
    AllocatedBytes.word_mapped source array (16*n) (16*index) actual.workspace.sha.domain arena (by omega) geometry.arrayAligned (by omega)
  have nMapped : source.memaddrs (array+BitVec.ofNat 64 (16*index+8)) :=
    AllocatedBytes.word_mapped source array (16*n) (16*index+8) actual.workspace.sha.domain arena (by omega) geometry.arrayAligned (by omega)
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
  simp only [evalListHOLFinite,transactionArguments,evalListHOLExact,pRead,nRead,outRead,PBytes.values]

end InitECandidate.Solver.Input.PayloadHash.Transactions

#print axioms InitECandidate.Solver.Input.PayloadHash.Transactions.RoundState.dec_clock
#print axioms InitECandidate.Solver.Input.PayloadHash.Transactions.call_geometry
#print axioms InitECandidate.Solver.Input.PayloadHash.Transactions.arguments_read
