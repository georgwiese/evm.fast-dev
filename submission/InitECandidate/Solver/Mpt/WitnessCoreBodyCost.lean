import InitECandidate.Solver.Mpt.WitnessCoreLoopBound
import InitECandidate.Solver.Mpt.WitnessCoreInitial
import InitECandidate.Solver.Mpt.WitnessRecordRank
import InitECandidate.Solver.Input.ClockCostCurrent

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
open Input.Main.RunAttemptConstructors

/-- The seven actual initial declarations establish the loop invariant
with empty stack and the exact current allocation frontier. -/
theorem initial_invariant (databaseData : Input.CurrentTable.NodeBuild.Data) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap cursor limit : BitVec 64) (database : Input.CurrentTable.NodeLookup.Database source databaseData)
    (tableBefore : (Input.CurrentTable.New.endPointer databaseData.table databaseData.cap).toNat≤heap.toNat) (databaseEq : db=databaseData.table)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0) (heapLower : 2701131776≤heap.toNat)
    (live : Rlp.LiveArena source) (arena : Rlp.Validation.Arena source cursor limit)
    (before : pointer.toNat+length.toNat≤db.toNat) (small : length.toNat≤1024) (lower : 2701131776≤pointer.toNat)
    (installed : Input.OriginalCode.Installed source.code) :
    Invariant databaseData heap.toNat db limit (ready source pointer length) ⟨heap,cursor,[],.decode,true⟩ := by
  have fields:=ready_fields source pointer length
  have actualDb:=(ready_other source pointer length (ofString "db") (by decide)).trans dbCell
  have readyDatabase:=database.of_frame (ready_erase source pointer length)
  have words : DataWords (ready source pointer length):=
    ⟨⟨pointer,fields.2.2.1⟩,⟨length,fields.2.2.2.1⟩,⟨0#64,fields.2.1⟩,⟨0#64,fields.2.2.2.2.2.1⟩⟩
  have waiting : Waiting []:=by intro entry member; cases member
  exact ⟨readyDatabase,tableBefore,databaseEq,actualDb,heapCell,heapArena,heapBound,aligned,heapLower,Nat.le_refl _,arena.of_fields source (ready source pointer length) cursor limit rfl rfl,
    live.of_frame rfl,empty _ db cursor.toNat heap.toNat,(by intro entry member; cases member),words,fields.1,fields.2.2.2.2.1,fields.2.2.2.2.2.2,
    ⟨waiting,pointer,length,fields.2.2.1,fields.2.2.2.1,small,lower,before⟩,Or.inl rfl,installed⟩

/-- Full unchanged original238 body, including its actual seven local
declarations, while loop, footer and lexical restorations, on every
outcome. The dynamic initial arena supplies a uniform rank<=6823154. -/
theorem body_cost (databaseData : Input.CurrentTable.NodeBuild.Data) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap cursor limit : BitVec 64) (database : Input.CurrentTable.NodeLookup.Database source databaseData)
    (tableBefore : (Input.CurrentTable.New.endPointer databaseData.table databaseData.cap).toNat≤heap.toNat) (databaseEq : db=databaseData.table)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0) (heapLower : 2701131776≤heap.toNat)
    (live : Rlp.LiveArena source) (arena : Rlp.Validation.Arena source cursor limit)
    (before : pointer.toNat+length.toNat≤db.toNat) (small : length.toNat≤1024) (lower : 2701131776≤pointer.toNat)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤(iterationCost+1)*6823154 := by
  have invariant:=initial_invariant databaseData source db pointer length heap cursor limit database tableBefore databaseEq dbCell heapCell heapArena heapBound aligned heapLower live arena before small lower installed
  have loopPaid:=invariant.loop_cost databaseData heap.toNat db limit (ready source pointer length) ⟨heap,cursor,[],.decode,true⟩
  have rankBound:=WitnessRecord.live_initial_rank_upper source cursor limit live arena
  have loopBound : (ready source pointer length).clock-(evaluateHOLFiniteState (ready source pointer length) (.while condition loopBody)).2.clock≤(iterationCost+1)*6823154:=
    loopPaid.trans (Nat.mul_le_mul_left (iterationCost+1) rankBound)
  have suffixPaid:=Input.ClockCost.sequence_current (ready source pointer length) (.while condition loopBody) footer ((iterationCost+1)*6823154) 0 loopBound
    (Input.ClockCost.returned _ (WitnessRadix.QueryBranch.localVar "result"))
  let output:=evaluateHOLFiniteState source body
  obtain ⟨restoreStack,inner,setup,continued,postEq,clockEq⟩:=initial_trace source output.2 pointer length pointerCell lengthCell output.1 rfl
  rw [continued] at suffixPaid
  change source.clock-inner.clock≤(iterationCost+1)*6823154+0 at suffixPaid
  change source.clock-output.2.clock≤(iterationCost+1)*6823154
  rw [clockEq]
  simpa only [Nat.add_zero] using suffixPaid

/-- Exact source call/loop allowance for the complete current core body. -/
theorem body_cost_value : (iterationCost+1)*6823154=1757412483164 := by decide

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.initial_invariant
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.body_cost

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.body_cost_value
