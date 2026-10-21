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
theorem initial_invariant (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap cursor limit : BitVec 64) (boundary : RootBoundary input source)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0) (heapLower : 2713731432≤heap.toNat)
    (arena : Rlp.Validation.Arena source cursor limit) (below : cursor.toNat≤2713717616)
    (before : pointer.toNat+length.toNat≤db.toNat) (small : length.toNat≤1024) (lower : 2713731432≤pointer.toNat)
    (installed : Input.OriginalCode.Installed source.code) :
    Invariant input heap.toNat db limit (ready source pointer length) ⟨heap,cursor,[],.decode,true⟩ := by
  have fields:=ready_fields source pointer length
  have actualDb:=(ready_other source pointer length (ofString "db") (by decide)).trans dbCell
  have frozen:=(boundary.freeze input source heap heapCell).frame input source (ready source pointer length) heap.toNat rfl rfl
    (ready_other source pointer length (ofString "db") (by decide)) (by intros; rfl)
  have words : DataWords (ready source pointer length):=
    ⟨⟨pointer,fields.2.2.1⟩,⟨length,fields.2.2.2.1⟩,⟨0#64,fields.2.1⟩,⟨0#64,fields.2.2.2.2.2.1⟩⟩
  have waiting : Waiting []:=by intro entry member; cases member
  exact ⟨frozen,actualDb,heapCell,heapArena,aligned,heapLower,Nat.le_refl _,arena.of_fields source (ready source pointer length) cursor limit rfl rfl,
    below,empty _ db cursor.toNat heap.toNat,(by intro entry member; cases member),words,fields.1,fields.2.2.2.2.1,fields.2.2.2.2.2.2,
    ⟨waiting,pointer,length,fields.2.2.1,fields.2.2.2.1,small,lower,before⟩,installed⟩

/-- Full unchanged original238 body, including its actual seven local
declarations, while loop, footer and lexical restorations, on every
outcome. The dynamic initial arena supplies a uniform rank<=6864962. -/
theorem body_cost (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap cursor limit : BitVec 64) (boundary : RootBoundary input source)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapLower : 2713731432≤heap.toNat)
    (arena : Rlp.Validation.Arena source cursor limit) (below : cursor.toNat≤2713717616)
    (before : pointer.toNat+length.toNat≤db.toNat) (small : length.toNat≤1024) (lower : 2713731432≤pointer.toNat)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤(iterationCost input+1)*6864962 := by
  have savedBoundary:=boundary
  obtain ⟨codeArray,nodes,codes,actualHeap,nodeData,codeData,nodeCell,actualCell,heapArena,aligned,nodeBefore,codeBefore⟩:=savedBoundary
  have heapEq : actualHeap=heap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualCell.symm.trans heapCell)))
  subst actualHeap
  have invariant:=initial_invariant input source db pointer length heap cursor limit boundary dbCell heapCell heapArena aligned heapLower arena below before small lower installed
  have loopPaid:=invariant.loop_cost input heap.toNat db limit (ready source pointer length) ⟨heap,cursor,[],.decode,true⟩
  have rankBound:=WitnessRecord.initial_rank_upper source cursor limit arena below
  have loopBound : (ready source pointer length).clock-(evaluateHOLFiniteState (ready source pointer length) (.while condition loopBody)).2.clock≤(iterationCost input+1)*6864962:=
    loopPaid.trans (Nat.mul_le_mul_left (iterationCost input+1) rankBound)
  have suffixPaid:=Input.ClockCost.sequence_current (ready source pointer length) (.while condition loopBody) footer ((iterationCost input+1)*6864962) 0 loopBound
    (Input.ClockCost.returned _ (WitnessRadix.QueryBranch.localVar "result"))
  let output:=evaluateHOLFiniteState source body
  obtain ⟨restoreStack,inner,setup,continued,postEq,clockEq⟩:=initial_trace source output.2 pointer length pointerCell lengthCell output.1 rfl
  rw [continued] at suffixPaid
  change source.clock-inner.clock≤(iterationCost input+1)*6864962+0 at suffixPaid
  change source.clock-output.2.clock≤(iterationCost input+1)*6864962
  rw [clockEq]
  exact suffixPaid.trans (by omega)

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.initial_invariant
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.body_cost
