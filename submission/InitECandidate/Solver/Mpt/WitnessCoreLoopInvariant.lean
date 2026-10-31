import InitECandidate.Solver.Mpt.WitnessCoreStackFrontier
import InitECandidate.Solver.Mpt.WitnessCoreStackDecode
import InitECandidate.Solver.Mpt.WitnessCoreStackResolve

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
open Input.Main.RunAttemptConstructors

structure Configuration where
  heap : BitVec 64
  cursor : BitVec 64
  stack : List Entry
  phase : WitnessStackRank.Phase
  running : Bool

def Configuration.rank (configuration : Configuration) (limit : BitVec 64) : Nat:=
  WitnessStackRank.rank (WitnessStackRank.recordsLeft configuration.cursor.toNat limit.toNat)
    (frames configuration.stack) configuration.phase configuration.running

def modeWord : WitnessStackRank.Phase→BitVec 64 | .returning=>0#64 | .decode=>1#64 | .resolve=>2#64
def goWord (running : Bool) : BitVec 64:=if running then 1#64 else 0#64

def PhaseInvariant (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frontier : Nat) (db heap : BitVec 64)
    (stack : List Entry) : WitnessStackRank.Phase→Prop
  | .decode=>Waiting stack ∧ ∃ pointer length,
      source.locals.lookup (ofString "cur_p")=some (.val (.word pointer)) ∧
      source.locals.lookup (ofString "cur_n")=some (.val (.word length)) ∧
      length.toNat≤1024 ∧ 2701131776≤pointer.toNat ∧ pointer.toNat+length.toNat≤db.toNat
  | .resolve=>∃ entry rest,stack=entry::rest ∧ Waiting rest ∧
      source.locals.lookup (ofString "slot")=some (.val (.word (BitVec.ofNat 64 entry.data.payload.slotIndex)))
  | .returning=>Waiting stack ∧ ∃ child,
      source.locals.lookup (ofString "result")=some (.val (.word child)) ∧
      ResultOwned source (max frontier (resultLower stack)) heap.toNat child

/-- Invariant of the unchanged original238 loop. Every physical record,
pending hash, allocation frontier and control binding comes from the
actual program state; the input hashes need not form an acyclic graph. -/
structure Invariant (databaseData : Input.CurrentTable.NodeBuild.Data) (frontier : Nat) (db limit : BitVec 64)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (configuration : Configuration) : Prop where
  database : Input.CurrentTable.NodeLookup.Database source databaseData
  tableBefore : (Input.CurrentTable.New.endPointer databaseData.table databaseData.cap).toNat≤frontier
  databaseEq : db=databaseData.table
  dbCell : source.locals.lookup (ofString "db")=some (.val (.word db))
  heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word configuration.heap))
  heapArena : AllocatedBytes.Arena configuration.heap 0
  heapBound : configuration.heap.toNat≤2952790016
  aligned : configuration.heap.toNat%8=0
  heapLower : 2701131776≤configuration.heap.toNat
  frontierBefore : frontier≤configuration.heap.toNat
  scratch : Rlp.Validation.Arena source configuration.cursor limit
  live : Rlp.LiveArena source
  view : View source db configuration.cursor.toNat configuration.heap.toNat configuration.stack
  fresh : FreshFrom frontier configuration.stack
  words : DataWords source
  topCell : source.locals.lookup (ofString "top")=some (.val (.word (top configuration.stack)))
  modeCell : source.locals.lookup (ofString "mode")=some (.val (.word (modeWord configuration.phase)))
  goCell : source.locals.lookup (ofString "go")=some (.val (.word (goWord configuration.running)))
  phase : PhaseInvariant source frontier db configuration.heap configuration.stack configuration.phase
  stopped : configuration.running=true ∨ configuration.stack=[] ∧ configuration.phase=.returning
  installed : Input.OriginalCode.Installed source.code

/-- The actual table image derives its ordinary nonwrapping header and
end. Its already-built extent precedes the fixed entry frontier and heap. -/
theorem Invariant.db_before (databaseData : Input.CurrentTable.NodeBuild.Data) (frontier : Nat) (db limit : BitVec 64)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (configuration : Configuration)
    (invariant : Invariant databaseData frontier db limit source configuration) : db.toNat≤configuration.heap.toNat := by
  obtain ⟨root,next,count,valid,bits,left,right,keys,image,bounded⟩:=invariant.database.image
  have a:=image.geometry.tableBefore
  have b:=image.geometry.keysBefore
  have c:=image.geometry.nodesBefore
  have d:=image.geometry.orderBefore
  have endBefore:=invariant.tableBefore.trans invariant.frontierBefore
  rw [invariant.databaseEq]
  omega

/-- Spending the real while tick changes only the source clock. It
retains the whole physical/phase/database invariant at the same rank. -/
theorem Invariant.dec_clock (databaseData : Input.CurrentTable.NodeBuild.Data) (frontier : Nat) (db limit : BitVec 64)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (configuration : Configuration)
    (invariant : Invariant databaseData frontier db limit source configuration) :
    Invariant databaseData frontier db limit (decClockHOLFinite source) configuration := by
  have database:=invariant.database.of_frame (show Input.LocalEffects.erase (decClockHOLFinite source)=Input.LocalEffects.erase source from rfl)
  have view:=invariant.view.of_fields source (decClockHOLFinite source) db configuration.cursor.toNat configuration.heap.toNat configuration.stack rfl rfl
  have words : DataWords (decClockHOLFinite source):=⟨invariant.words.pointer,invariant.words.length,invariant.words.result,invariant.words.slot⟩
  have phase : PhaseInvariant (decClockHOLFinite source) frontier db configuration.heap configuration.stack configuration.phase:=by
    have old:=invariant.phase
    cases phaseEq : configuration.phase with
    | decode=>
      simp only [phaseEq,PhaseInvariant] at old ⊢
      obtain ⟨waiting,pointer,length,pointerCell,lengthCell,small,lower,before⟩:=old
      exact ⟨waiting,pointer,length,pointerCell,lengthCell,small,lower,before⟩
    | resolve=>
      simp only [phaseEq,PhaseInvariant] at old ⊢
      obtain ⟨entry,rest,stackEq,waiting,slot⟩:=old
      exact ⟨entry,rest,stackEq,waiting,slot⟩
    | returning=>
      simp only [phaseEq,PhaseInvariant] at old ⊢
      obtain ⟨waiting,child,result,owned⟩:=old
      exact ⟨waiting,child,result,owned.of_fields source (decClockHOLFinite source) child (max frontier (resultLower configuration.stack)) configuration.heap.toNat rfl⟩
  exact ⟨database,invariant.tableBefore,invariant.databaseEq,invariant.dbCell,invariant.heapCell,invariant.heapArena,invariant.heapBound,invariant.aligned,invariant.heapLower,invariant.frontierBefore,
    invariant.scratch.of_fields source (decClockHOLFinite source) configuration.cursor limit rfl rfl,invariant.live.of_frame rfl,view,invariant.fresh,words,
    invariant.topCell,invariant.modeCell,invariant.goCell,phase,invariant.stopped,invariant.installed⟩

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.Invariant.db_before
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.Invariant.dec_clock
