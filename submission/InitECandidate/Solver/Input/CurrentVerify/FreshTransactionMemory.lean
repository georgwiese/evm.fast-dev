import InitECandidate.Solver.Input.PersistentAllocationFrame
import InitECandidate.Solver.Mpt.AccountDecodeFieldsNormal
import InitECandidate.Solver.Mpt.AccountNewCost
import InitECandidate.Solver.Mpt.AccountDecodeCall
import InitECandidate.Solver.Input.ScopedCallData
import InitECandidate.Solver.WitnessRadix.AllocationGlobals
import InitECandidate.Solver.Mpt.TrieLookupCallValues
import InitECandidate.Solver.Input.ScalarArgumentsLookup
import InitECandidate.Solver.Input.CurrentTable.Set.Scalar
import InitECandidate.Solver.Input.CurrentVerify.BlockExecution

namespace InitECandidate.Solver.Input.CurrentVerify.FreshTransaction
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

structure TableSpec where
  key : BitVec 64
  cap : BitVec 64
  offset : Nat
  deriving DecidableEq

def TableSpec.Valid (spec : TableSpec) : Prop :=
  8≤spec.offset ∧ spec.offset<72 ∧ spec.offset%8=0 ∧ 2≤spec.cap.toNat

def TableSpec.arguments (spec : TableSpec) : List (ExpHOL 64):=[.const spec.key,.const spec.cap]
def field (offset : Nat) : ExpHOL 64:=Scalar.plus (.var .global (ofString "ts")) offset

def firstTable : TableSpec:=⟨20#64,64#64,8⟩
def remainingTables : List TableSpec:=
  [⟨20#64,64#64,16⟩,⟨52#64,64#64,24⟩,⟨20#64,16#64,32⟩,⟨52#64,16#64,40⟩,
   ⟨32#64,16#64,48⟩,⟨20#64,16#64,56⟩,⟨52#64,16#64,64⟩]
def tables : List TableSpec:=firstTable::remainingTables

def Images (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record heap : BitVec 64) (done : List TableSpec) : Prop :=
  ∀ spec∈done,∃ table,source.memory (record+BitVec.ofNat 64 spec.offset)=.word table ∧
    CurrentTable.New.ScalarEmpty source table spec.key spec.cap ∧ record.toNat+72≤table.toNat ∧ table.toNat+88≤heap.toNat ∧
    (CurrentTable.New.scalarNextHeap table spec.key spec.cap).toNat≤heap.toNat

/-- Distinct real transaction-table fields refer to disjoint complete
constructor regions, including the key/node/order backing arrays. -/
def Separated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record : BitVec 64) (done : List TableSpec) : Prop :=
  ∀ left∈done,∀ right∈done,left.offset≠right.offset→∃ leftTable rightTable,
    source.memory (record+BitVec.ofNat 64 left.offset)=.word leftTable ∧
    source.memory (record+BitVec.ofNat 64 right.offset)=.word rightTable ∧
    ((CurrentTable.New.scalarNextHeap leftTable left.key left.cap).toNat≤rightTable.toNat ∨
      (CurrentTable.New.scalarNextHeap rightTable right.key right.cap).toNat≤leftTable.toNat)

theorem Separated.of_memory {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {record : BitVec 64} {done : List TableSpec}
    (separated : Separated source record done)
    (memory : ∀ spec∈done,target.memory (record+BitVec.ofNat 64 spec.offset)=source.memory (record+BitVec.ofNat 64 spec.offset)) :
    Separated target record done := by
  intro left lm right rm different
  obtain ⟨leftTable,rightTable,lc,rc,before⟩:=separated left lm right rm different
  exact ⟨leftTable,rightTable,(memory left lm).trans lc,(memory right rm).trans rc,before⟩

/-- Actual partially constructed transaction state. All completed tables
are initialized images below the current live heap. The original earlier
memory and unrelated globals remain tied to this same call's entry state. -/
structure Context (origin source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record bs heap : BitVec 64) (done : List TableSpec) : Prop where
  runtime : CurrentStartup.ArenaState source
  recordCell : source.globals.lookup (ofString "ts")=some (.val (.word record))
  recordArena : AllocatedBytes.Arena record 72
  recordAligned : record.toNat%8=0
  heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  heapArena : AllocatedBytes.Arena heap 0
  heapBound : heap.toNat≤2952790016
  heapAligned : heap.toNat%8=0
  afterRecord : record.toNat+72≤heap.toNat
  blockField : source.memory record=.word bs
  valid : ∀ spec∈done,spec.Valid
  images : Images source record heap done
  older : PersistentMemoryFrame origin source record
  globals : ∀ name : MlS,name≠ofString "heap_ptr"→name≠ofString "ts"→name≠ofString "journal_n"→
    source.globals.lookup name=origin.globals.lookup name
  separated : Separated source record done

theorem record_address_number (record : BitVec 64) (arena : AllocatedBytes.Arena record 72) (offset : Nat) (inside : offset<72) :
    (record+BitVec.ofNat 64 offset).toNat=record.toNat+offset := by
  exact byteAddress_toNat record offset (by have upper:=arena.upper; omega)

theorem record_addresses_distinct (record : BitVec 64) (arena : AllocatedBytes.Arena record 72)
    (left right : Nat) (leftInside : left<72) (rightInside : right<72) (different : left≠right) :
    record+BitVec.ofNat 64 left≠record+BitVec.ofNat 64 right := by
  intro same
  have numbers:=congrArg BitVec.toNat same
  rw [record_address_number record arena left leftInside,record_address_number record arena right rightInside] at numbers
  omega

theorem header_away_record {source : PanSemStateFiniteExact 64 Guest.HostMemory} (record table key cap : BitVec 64)
    (recordArena : AllocatedBytes.Arena record 72) (image : CurrentTable.New.ScalarEmpty source table key cap)
    (before : record.toNat+72≤table.toNat) (offset : Nat) (inside : offset<72)
    (entry : BitVec 64×BitVec 64) (member : entry∈CurrentTable.New.scalarWrites table key cap) :
    entry.1≠record+BitVec.ofNat 64 offset := by
  have lower:=CurrentTable.New.scalar_write_lower table key cap entry image.geometry.table member
  have number:=record_address_number record recordArena offset inside
  intro same
  have equal:=congrArg BitVec.toNat same
  rw [number] at equal
  omega

/-- Every normal persistent constructor preserves all previously completed
record fields/table images and advances this same physical construction. -/
theorem Context.after_persistent {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {record bs heap : BitVec 64} {done : List TableSpec}
    (context : Context origin source record bs heap done) (frame : PersistentNormalFrame source post heap) :
    ∃ next,Context origin post record bs next done := by
  obtain ⟨next,cell,owned,bounded,aligned,advanced⟩:=frame.nextHeap
  have older:=context.older.trans origin source post record heap frame.memory_frame (by have before:=context.afterRecord; omega)
  refine ⟨next,frame.current_arena context.runtime,(frame.globals _ (by decide)).trans context.recordCell,
    context.recordArena,context.recordAligned,cell,owned,bounded,aligned,by have before:=context.afterRecord; omega,
    (frame.memory record (by have before:=context.afterRecord; omega)).trans context.blockField,context.valid,?_,older,?_,?_⟩
  · intro spec member
    obtain ⟨table,pointer,image,beforeTable,beforeHeap,endBeforeHeap⟩:=context.images spec member
    have number:=record_address_number record context.recordArena spec.offset (context.valid spec member).2.1
    refine ⟨table,(frame.memory _ (by rw [number]; have before:=context.afterRecord; have inside:=(context.valid spec member).2.1; omega)).trans pointer,
      image.of_persistent beforeHeap frame.memory_frame,beforeTable,by omega,by omega⟩
  · intro name notHeap notRecord notCounter
    exact (frame.globals name notHeap).trans (context.globals name notHeap notRecord notCounter)
  · apply context.separated.of_memory
    intro spec member
    apply frame.memory
    rw [record_address_number record context.recordArena spec.offset (context.valid spec member).2.1]
    have before:=context.afterRecord
    have inside:=(context.valid spec member).2.1
    omega

/-- Lexical restoration changes none of these physical facts. -/
theorem Context.of_erase {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {record bs heap : BitVec 64} {done : List TableSpec}
    (context : Context origin source record bs heap done) (same : LocalEffects.erase post=LocalEffects.erase source) :
    Context origin post record bs heap done := by
  have memory:=LocalEffects.memory_of_erase source post same
  have globals:=congrArg PanSemStateFiniteExact.globals same
  change post.globals=source.globals at globals
  refine ⟨context.runtime.of_frame same,by rw [globals]; exact context.recordCell,context.recordArena,context.recordAligned,
    by rw [globals]; exact context.heapCell,context.heapArena,context.heapBound,context.heapAligned,context.afterRecord,
    by rw [memory]; exact context.blockField,context.valid,?_,context.older.of_erase origin source origin post record rfl same,?_,context.separated.of_memory (by intro spec member; rw [memory])⟩
  · intro spec member
    obtain ⟨table,pointer,image,beforeTable,beforeHeap,endBeforeHeap⟩:=context.images spec member
    exact ⟨table,by rw [memory]; exact pointer,image.of_erase same,beforeTable,beforeHeap,endBeforeHeap⟩
  · intro name notHeap notRecord notCounter
    rw [globals]
    exact context.globals name notHeap notRecord notCounter

/-- The actual final journal reset retains all constructed tables. -/
theorem Context.reset {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {record bs heap : BitVec 64} {done : List TableSpec}
    (context : Context origin source record bs heap done) :
    Context origin (putGlobal source "journal_n" 0#64) record bs heap done := by
  have runtime : CurrentStartup.ArenaState (putGlobal source "journal_n" 0#64):=
    ⟨(putGlobal.lookup_other source "journal_n" 0#64 _ (by decide)).trans context.runtime.scratch,
      (putGlobal.lookup_other source "journal_n" 0#64 _ (by decide)).trans context.runtime.frame,context.runtime.domain,context.runtime.code⟩
  refine ⟨runtime,(putGlobal.lookup_other source "journal_n" 0#64 _ (by decide)).trans context.recordCell,
    context.recordArena,context.recordAligned,(putGlobal.lookup_other source "journal_n" 0#64 _ (by decide)).trans context.heapCell,
    context.heapArena,context.heapBound,context.heapAligned,context.afterRecord,context.blockField,context.valid,?_,
    context.older.put_global origin source record "journal_n" 0#64 (by decide),?_,context.separated⟩
  · intro spec member
    obtain ⟨table,pointer,image,beforeTable,beforeHeap,endBeforeHeap⟩:=context.images spec member
    exact ⟨table,pointer,image.of_memory rfl (by intros; rfl),beforeTable,beforeHeap,endBeforeHeap⟩
  · intro name notHeap notRecord notCounter
    exact (putGlobal.lookup_other source "journal_n" 0#64 name notCounter).trans (context.globals name notHeap notRecord notCounter)

/-- Each actual pointer store preserves every earlier completed field and
header and adds the just-constructed table to the physical transaction. -/
theorem Context.stored_table {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {record bs heap : BitVec 64} {done : List TableSpec}
    (context : Context origin source record bs heap done) (spec : TableSpec) (valid : spec.Valid)
    (different : ∀ old∈done,old.offset≠spec.offset) (table : BitVec 64)
    (image : CurrentTable.New.ScalarEmpty source table spec.key spec.cap)
    (beforeTable : record.toNat+72≤table.toNat) (beforeHeap : table.toNat+88≤heap.toNat)
    (endBeforeHeap : (CurrentTable.New.scalarNextHeap table spec.key spec.cap).toNat≤heap.toNat)
    (olderBeforeTable : ∀ old∈done,∃ oldTable,source.memory (record+BitVec.ofNat 64 old.offset)=.word oldTable ∧
      (CurrentTable.New.scalarNextHeap oldTable old.key old.cap).toNat≤table.toNat)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (normal : evaluateHOLFiniteState source (.store (field spec.offset) (localVar "t"))=(none,post)) :
    Context origin post record bs heap (done++[spec]) := by
  have recordRead : eval source (.var .global (ofString "ts"))=some (.val (.word record)):=by
    simp [eval,evalHOLExact,context.recordCell]
  have addressRead:=Scalar.plus_read source (.var .global (ofString "ts")) record spec.offset recordRead
  have tableRead:=Request.local_word source "t" table tableCell
  obtain ⟨mapped,endpoint⟩:=word_store_normal source post (field spec.offset) (localVar "t") _ table addressRead tableRead normal
  have number:=record_address_number record context.recordArena spec.offset valid.2.1
  have older:=context.older.store_after origin source post record (field spec.offset) (localVar "t") _ table addressRead tableRead
    (by rw [number]; omega) normal
  rw [endpoint] at older ⊢
  let written : PanSemStateFiniteExact 64 Guest.HostMemory:=
    {source with memory:=StoreWord.put source.memory (record+BitVec.ofNat 64 spec.offset) table}
  change Context origin written record bs heap (done++[spec])
  have away : record≠record+BitVec.ofNat 64 spec.offset:=by
    simpa only [BitVec.add_zero] using record_addresses_distinct record context.recordArena 0 spec.offset (by decide) valid.2.1 (by have lower:=valid.1; omega)
  have keepImage (oldTable key cap : BitVec 64) (oldImage : CurrentTable.New.ScalarEmpty source oldTable key cap)
      (afterRecord : record.toNat+72≤oldTable.toNat) : CurrentTable.New.ScalarEmpty written oldTable key cap := by
    apply oldImage.of_memory (target:=written) rfl
    intro entry member
    exact if_neg (header_away_record record oldTable key cap context.recordArena oldImage afterRecord spec.offset valid.2.1 entry member)
  refine ⟨⟨context.runtime.scratch,context.runtime.frame,context.runtime.domain,context.runtime.code⟩,context.recordCell,context.recordArena,context.recordAligned,context.heapCell,context.heapArena,
    context.heapBound,context.heapAligned,context.afterRecord,?_,?_,?_,older,context.globals,?_⟩
  · change StoreWord.put source.memory (record+BitVec.ofNat 64 spec.offset) table record=.word bs
    rw [StoreWord.put,if_neg away]
    exact context.blockField
  · intro old member
    rcases List.mem_append.mp member with previous|last
    · exact context.valid old previous
    · have same : old=spec:=by simpa only [List.mem_singleton] using last
      simpa only [same] using valid
  · intro old member
    rcases List.mem_append.mp member with previous|last
    · obtain ⟨oldTable,pointer,oldImage,oldBeforeTable,oldBeforeHeap,oldEndBeforeHeap⟩:=context.images old previous
      have fieldAway:=record_addresses_distinct record context.recordArena old.offset spec.offset
        (context.valid old previous).2.1 valid.2.1 (different old previous)
      refine ⟨oldTable,?_,keepImage oldTable old.key old.cap oldImage oldBeforeTable,oldBeforeTable,oldBeforeHeap,oldEndBeforeHeap⟩
      change StoreWord.put source.memory (record+BitVec.ofNat 64 spec.offset) table (record+BitVec.ofNat 64 old.offset)=.word oldTable
      rw [StoreWord.put,if_neg fieldAway]
      exact pointer
    · have same : old=spec:=by simpa only [List.mem_singleton] using last
      subst old
      exact ⟨table,by simp [written,StoreWord.put],keepImage table spec.key spec.cap image beforeTable,beforeTable,beforeHeap,endBeforeHeap⟩
  · have kept (old : TableSpec) (member : old∈done) :
        written.memory (record+BitVec.ofNat 64 old.offset)=source.memory (record+BitVec.ofNat 64 old.offset):=by
      exact if_neg (record_addresses_distinct record context.recordArena old.offset spec.offset
        (context.valid old member).2.1 valid.2.1 (different old member))
    have stored : written.memory (record+BitVec.ofNat 64 spec.offset)=.word table:=by simp [written,StoreWord.put]
    intro left lm right rm distinct
    rcases List.mem_append.mp lm with lm|lm <;> rcases List.mem_append.mp rm with rm|rm
    · exact (context.separated.of_memory kept) left lm right rm distinct
    · have same : right=spec:=by simpa only [List.mem_singleton] using rm
      subst right
      obtain ⟨oldTable,cell,before⟩:=olderBeforeTable left lm
      exact ⟨oldTable,table,(kept left lm).trans cell,stored,Or.inl before⟩
    · have same : left=spec:=by simpa only [List.mem_singleton] using lm
      subst left
      obtain ⟨oldTable,cell,before⟩:=olderBeforeTable right rm
      exact ⟨table,oldTable,stored,(kept right rm).trans cell,Or.inr before⟩
    · have l : left=spec:=by simpa only [List.mem_singleton] using lm
      have r : right=spec:=by simpa only [List.mem_singleton] using rm
      exact False.elim (distinct (by rw [l,r]))

def tableCall (spec : TableSpec) : ProgHOL 64:=
  .call (some (some (.local,ofString "t"),none)) (ofString "htab_new") spec.arguments
def tableStore (spec : TableSpec) : ProgHOL 64:=.store (field spec.offset) (localVar "t")
def reset : ProgHOL 64:=.assign .global (ofString "journal_n") (.const 0#64)
def tailProgram : List TableSpec → ProgHOL 64
  | []=>.seq reset (.return (.const 0#64))
  | spec::specs=>.seq (tableCall spec) (.seq (tableStore spec) (tailProgram specs))

def Tail (specs : List TableSpec) : Prop:=
  ∀ origin source post record bs heap done,Context origin source record bs heap done →
    (∀ spec∈specs,spec.Valid) → ((specs.map TableSpec.offset).Nodup) →
    (∀ old∈done,∀ future∈specs,old.offset≠future.offset) → ∀ value,
    evaluateHOLFiniteState source (tailProgram specs)=(some (.returned value),post) →
    value=.val (.word 0#64) ∧ ∃ next,Context origin post record bs next (done++specs) ∧
      post.globals.lookup (ofString "journal_n")=some (.val (.word 0#64))

/-- Replay the actual remaining constructor/store commands in order. Each
normal call supplies its own allocation room; completed images are retained
through each subsequent actual constructor, store and final reset/return. -/
theorem tail_normal (specs : List TableSpec) : Tail specs := by
  induction specs with
  | nil=>
    intro origin source post record bs heap done context valid distinct different value normal
    have safe : LocalPrefix (ofString "_") reset:=.globalAssign _ _
    obtain ⟨middle,resetRun,returned,saved⟩:=safe.normal_continue source post (.return (.const 0#64)) value normal
    have middleEq:=global_assign_none source middle "journal_n" (.const 0#64) 0#64 rfl resetRun
    have current : Context origin middle record bs heap done:=by rw [middleEq]; exact context.reset
    obtain ⟨read,endpoint⟩:=return_normal middle post (.const 0#64) value returned
    have finalContext:=current.of_erase (post:=post) (by rw [endpoint]; rfl)
    refine ⟨Option.some.inj read.symm,heap,?_,?_⟩
    · simpa only [List.append_nil] using finalContext
    · rw [endpoint,middleEq]
      exact putGlobal.lookup_same source "journal_n" 0#64
  | cons spec specs ih=>
    intro origin source post record bs heap done context valid distinct different value normal
    have validSpec:=valid spec (by simp)
    have safe : LocalPrefix (ofString "_") (tableCall spec):=
      .call (some (ofString "t")) _ _ (by intro name same; cases Option.some.inj same; decide)
    obtain ⟨middle,callRun,afterCall,saved⟩:=safe.normal_continue source post (.seq (tableStore spec) (tailProgram specs)) value normal
    obtain ⟨tableCell,image,nextCell,frame⟩:=CurrentTable.New.local_scalar_empty source middle "t" spec.key spec.cap heap spec.arguments rfl validSpec.2.2.2
      context.heapCell context.heapArena context.heapBound context.heapAligned context.runtime callRun
    obtain ⟨next,current⟩:=context.after_persistent frame
    have nextEq : next=CurrentTable.New.scalarNextHeap heap spec.key spec.cap:=by
      have equality:=current.heapCell.symm.trans nextCell
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using equality
    have beforeHeap : heap.toNat+88≤next.toNat:=by rw [nextEq]; exact image.geometry.header_before_end
    have storeSafe : LocalPrefix (ofString "_") (tableStore spec):=.store _ _
    obtain ⟨stored,storeRun,continued,kept⟩:=storeSafe.normal_continue middle post (tailProgram specs) value afterCall
    have entered:=current.stored_table spec validSpec (by intro old member; exact different old member spec (by simp))
      heap image context.afterRecord beforeHeap (by rw [nextEq]) (by
        intro old member
        obtain ⟨oldTable,pointer,oldImage,oldBeforeTable,oldBeforeHeap,oldEnd⟩:=context.images old member
        refine ⟨oldTable,(frame.memory _ ?_).trans pointer,oldEnd⟩
        rw [record_address_number record context.recordArena old.offset (context.valid old member).2.1]
        have afterRecord:=context.afterRecord
        have inside:=(context.valid old member).2.1
        omega) tableCell storeRun
    have pieces:=List.nodup_cons.mp distinct
    have separation : ∀ old∈done++[spec],∀ future∈specs,old.offset≠future.offset:=by
      intro old member future futureMember
      rcases List.mem_append.mp member with previous|last
      · exact different old previous future (List.mem_cons_of_mem spec futureMember)
      · have same : old=spec:=by simpa only [List.mem_singleton] using last
        subst old
        intro equal
        exact pieces.1 (List.mem_map.mpr ⟨future,futureMember,equal.symm⟩)
    obtain ⟨valueEq,last,finished,counter⟩:=ih origin stored post record bs next (done++[spec]) entered
      (by intro future member; exact valid future (List.mem_cons_of_mem spec member)) pieces.2 separation value continued
    refine ⟨valueEq,last,?_,counter⟩
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using finished

def allocateRecord : ProgHOL 64:=.call (some (some (.global,ofString "ts"),none)) (ofString "alloc") [.const 72#64]
def afterFirst : ProgHOL 64:=.seq (tableStore firstTable) (tailProgram remainingTables)
def beforeFirst : ProgHOL 64:=.decCall (ofString "t") .one (ofString "htab_new") firstTable.arguments afterFirst
def afterAllocation : ProgHOL 64:=.seq (.store (field 0) (.var .global (ofString "bs"))) beforeFirst

theorem body_shape : body=.seq allocateRecord afterAllocation := by
  simp only [body,allocateRecord,afterAllocation,beforeFirst,afterFirst,tableStore,field,firstTable,remainingTables,tailProgram,
    tableCall,TableSpec.arguments,reset,Guest.Software.guestFn_state_fresh_tx,progToHOL,expToHOL,shapeToHOL,
    Option.map_some,Option.map_none,List.map_cons,List.map_nil,Scalar.plus,localVar]

theorem specs_valid : ∀ spec∈tables,spec.Valid := by
  intro spec member
  simp only [tables,firstTable,remainingTables,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold TableSpec.Valid <;> decide

theorem offsets_distinct : (tables.map TableSpec.offset).Nodup := by decide

/-- The genuine first scoped constructor feeds the same physical sequence
as every later table. Its original lexical restoration retains all images. -/
theorem first_normal {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {record bs heap : BitVec 64} (context : Context origin source record bs heap [])
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source beforeFirst=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ ∃ next,Context origin post record bs next tables ∧
      post.globals.lookup (ofString "journal_n")=some (.val (.word 0#64)) := by
  obtain ⟨callee,called,keyLocal,capLocal⟩:=word_pair_environment source.code.lookup (ofString "htab_new")
    (ofString "key_len") (ofString "cap") CurrentTable.New.body .one firstTable.key firstTable.cap (by decide)
    (CurrentTable.New.original_code source.code context.runtime.code)
  obtain ⟨funded,target,answer,inner,bodyRun,checked,continued,endpoint⟩:=CallNormal.scoped_normal source post "t" .one (ofString "htab_new")
    firstTable.arguments _ CurrentTable.New.body afterFirst callee .one rfl called value normal
  obtain ⟨answerEq,image,nextCell,frame⟩:=CurrentTable.New.body_scalar_empty (callEntryStateHOLFinite source callee) target heap firstTable.key firstTable.cap
    keyLocal capLocal (by decide) context.heapCell context.heapArena context.heapBound context.heapAligned (context.runtime.of_frame rfl) answer bodyRun
  rw [answerEq] at continued
  let current:=CallNormal.continuationEntry source target "t" (.val (.word heap))
  have callerFrame : PersistentNormalFrame source current heap:=frame.of_erase _ _ source current heap rfl rfl
  obtain ⟨next,currentContext⟩:=context.after_persistent callerFrame
  have currentImage : CurrentTable.New.ScalarEmpty current heap firstTable.key firstTable.cap:=image.of_erase rfl
  have currentNext : current.globals.lookup (ofString "heap_ptr")=some (.val (.word (CurrentTable.New.scalarNextHeap heap firstTable.key firstTable.cap))):=nextCell
  have nextEq : next=CurrentTable.New.scalarNextHeap heap firstTable.key firstTable.cap:=by
    have equality:=currentContext.heapCell.symm.trans currentNext
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using equality
  have beforeHeap : heap.toNat+88≤next.toNat:=by rw [nextEq]; exact image.geometry.header_before_end
  have tableCell:=CallNormal.continuation_lookup_same source target "t" (.val (.word heap))
  have safe : LocalPrefix (ofString "_") (tableStore firstTable):=.store _ _
  obtain ⟨stored,storeRun,tailRun,kept⟩:=safe.normal_continue current inner (tailProgram remainingTables) value continued
  have entered:=currentContext.stored_table firstTable (specs_valid firstTable (by simp [tables])) (by intro old member; cases member)
    heap currentImage context.afterRecord beforeHeap (by rw [nextEq]) (by intro old member; cases member) tableCell storeRun
  have pieces:=List.nodup_cons.mp offsets_distinct
  have separation : ∀ old∈[firstTable],∀ future∈remainingTables,old.offset≠future.offset:=by
    intro old member future futureMember
    have same : old=firstTable:=by simpa only [List.mem_singleton] using member
    subst old
    intro equal
    exact pieces.1 (List.mem_map.mpr ⟨future,futureMember,equal.symm⟩)
  obtain ⟨valueEq,last,finished,counter⟩:=tail_normal remainingTables origin stored inner record bs next [firstTable] entered
    (by intro spec member; exact specs_valid spec (List.mem_cons_of_mem firstTable member)) pieces.2 separation value tailRun
  change Context origin inner record bs last tables at finished
  refine ⟨valueEq,last,finished.of_erase (by rw [endpoint]; rfl),?_⟩
  rw [endpoint]
  exact counter

/-- Complete actual current transaction-state construction. The real record
allocation and first store establish the forward invariant, then the eight
normal constructors establish every physical table image and pointer field.
Only incoming arena/heap invariants and the actual scalar block-state global
are entry conditions; no future room, results or initialized nodes are assumed. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (record bs : BitVec 64)
    (runtime : CurrentStartup.ArenaState source)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word record)))
    (heapArena : AllocatedBytes.Arena record 0) (heapBound : record.toNat≤2952790016) (heapAligned : record.toNat%8=0)
    (blockState : source.globals.lookup (ofString "bs")=some (.val (.word bs)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ ∃ next,Context source post record bs next tables ∧
      post.globals.lookup (ofString "journal_n")=some (.val (.word 0#64)) := by
  rw [body_shape] at normal
  have safe : LocalPrefix (ofString "_") allocateRecord:=.globalCall _ _ _
  obtain ⟨allocated,allocatedRun,afterRun,saved⟩:=safe.normal_continue source post afterAllocation value normal
  obtain ⟨locals,recordCell,owned,runtime1,frame,extent,globals⟩:=ExecuteBlock.allocation_global_memory_normal source allocated "ts" record 72#64
    [.const 72#64] rfl heapCell heapArena heapBound runtime (by decide) allocatedRun
  have storeSafe : LocalPrefix (ofString "_") (.store (field 0) (.var .global (ofString "bs"))):=.store _ _
  obtain ⟨stored,storeRun,continued,kept⟩:=storeSafe.normal_continue allocated post beforeFirst value afterRun
  have blockCell : allocated.globals.lookup (ofString "bs")=some (.val (.word bs)):=
    (globals _ (by decide) (by decide)).trans blockState
  have recordRead : eval allocated (.var .global (ofString "ts"))=some (.val (.word record)):=by
    simp [eval,evalHOLExact,recordCell]
  have addressRead:=Scalar.plus_read allocated (.var .global (ofString "ts")) record 0 recordRead
  have blockRead : eval allocated (.var .global (ofString "bs"))=some (.val (.word bs)):=by
    simp [eval,evalHOLExact,blockCell]
  obtain ⟨mapped,endpoint⟩:=word_store_normal allocated stored (field 0) (.var .global (ofString "bs")) _ bs addressRead blockRead storeRun
  have older:=frame.store_after source allocated stored record (field 0) (.var .global (ofString "bs")) _ bs addressRead blockRead
    (by simp only [BitVec.add_zero]; omega) storeRun
  obtain ⟨heap,current,before⟩:=ExecuteBlock.BalHeap.of_extent allocated (record.toNat+72) runtime1 (by have low:=heapArena.lower; omega) extent
  have entered : Context source stored record bs heap []:=by
    rw [endpoint] at older ⊢
    refine ⟨⟨runtime1.scratch,runtime1.frame,runtime1.domain,runtime1.code⟩,recordCell,owned,heapAligned,current.cell,current.arena,
      current.bounded,current.aligned,before,?_,?_,?_,older,?_,?_⟩
    · simp [StoreWord.put]
    · intro spec impossible; cases impossible
    · intro spec impossible; cases impossible
    · intro name notHeap notRecord notCounter
      exact globals name notRecord notHeap
    · intro left member; cases member
  exact first_normal entered value continued

/-- The entry-state reference can be restored from the genuine ordinary
caller's nonlocal entry relation; it does not depend on callee local bindings. -/
theorem Context.of_origin {origin origin' source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {record bs heap : BitVec 64} {done : List TableSpec}
    (context : Context origin source record bs heap done) (same : LocalEffects.erase origin'=LocalEffects.erase origin) :
    Context origin' source record bs heap done := by
  have globals:=congrArg PanSemStateFiniteExact.globals same
  change origin'.globals=origin.globals at globals
  refine {context with older:=context.older.of_erase origin source origin' source record same rfl,globals:=?_}
  intro name notHeap notRecord notCounter
  rw [globals]
  exact context.globals name notHeap notRecord notCounter

/-- Actual normal ignored state_fresh_tx caller, with the same eight table
images, restored caller locals and complete protection of older memory. -/
theorem call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (record bs : BitVec 64)
    (runtime : CurrentStartup.ArenaState source)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word record)))
    (heapArena : AllocatedBytes.Arena record 0) (heapBound : record.toNat≤2952790016) (heapAligned : record.toNat%8=0)
    (blockState : source.globals.lookup (ofString "bs")=some (.val (.word bs)))
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "state_fresh_tx") [])=(none,post)) :
    ∃ next,Context source post record bs next tables ∧
      post.globals.lookup (ofString "journal_n")=some (.val (.word 0#64)) ∧ post.locals=source.locals := by
  obtain ⟨funded,values,actual,callee,shape,target,value,args,called,bodyRun,checked,endpoint,fields⟩:=CallNormal.ignored_data source post (ofString "state_fresh_tx") [] normal
  have valuesEq : values=[]:=by
    change some ([] : List (ValueHOL 64))=some values at args
    exact Option.some.inj args.symm
  subst values
  have bodyEq:=LocalEffects.lookup_body source.code (ofString "state_fresh_tx") [] body .one (original_code source.code runtime.code) [] actual callee shape called
  rw [bodyEq] at bodyRun
  obtain ⟨valueEq,next,physical,counter⟩:=body_normal (callEntryStateHOLFinite source callee) target record bs (runtime.of_frame rfl)
    heapCell heapArena heapBound heapAligned blockState value bodyRun
  have callerContext : Context source target record bs next tables:=physical.of_origin rfl
  refine ⟨next,callerContext.of_erase (by rw [endpoint]; rfl),?_,?_⟩
  · rw [endpoint]; exact counter
  · rw [endpoint]

/-- The pointer values already read from distinct real transaction fields
have disjoint complete table regions, including all backing arrays. -/
theorem Context.tables_separated {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {record bs heap : BitVec 64} {done : List TableSpec} (context : Context origin source record bs heap done)
    (left right : TableSpec) (lm : left∈done) (rm : right∈done) (different : left.offset≠right.offset)
    (leftTable rightTable : BitVec 64)
    (lc : source.memory (record+BitVec.ofNat 64 left.offset)=.word leftTable)
    (rc : source.memory (record+BitVec.ofNat 64 right.offset)=.word rightTable) :
    (CurrentTable.New.scalarNextHeap leftTable left.key left.cap).toNat≤rightTable.toNat ∨
      (CurrentTable.New.scalarNextHeap rightTable right.key right.cap).toNat≤leftTable.toNat := by
  obtain ⟨l,r,lCell,rCell,separate⟩:=context.separated left lm right rm different
  have ls : l=leftTable:=HolWordLab.word.inj (lCell.symm.trans lc)
  have rs : r=rightTable:=HolWordLab.word.inj (rCell.symm.trans rc)
  simpa only [ls,rs] using separate

/-- Any header word of a distinct current table is outside the first
insertion's complete constructor region. The table pointers are the real
values read from this transaction's fields. -/
theorem Context.other_header_outside {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {record bs heap : BitVec 64} {done : List TableSpec} (context : Context origin source record bs heap done)
    (left right : TableSpec) (lm : left∈done) (rm : right∈done) (different : left.offset≠right.offset)
    (leftTable rightTable : BitVec 64)
    (lc : source.memory (record+BitVec.ofNat 64 left.offset)=.word leftTable)
    (rc : source.memory (record+BitVec.ofNat 64 right.offset)=.word rightTable)
    (rightImage : CurrentTable.New.ScalarEmpty source rightTable right.key right.cap) (offset : Nat) (inside : offset<88) :
    CurrentTable.New.OutsideScalar leftTable left.key left.cap (rightTable+BitVec.ofNat 64 offset) := by
  have number:=byteAddress_toNat rightTable offset (by have upper:=rightImage.geometry.table.upper; omega)
  change (rightTable+BitVec.ofNat 64 offset).toNat=rightTable.toNat+offset at number
  rcases context.tables_separated left right lm rm different leftTable rightTable lc rc with before|after
  · exact Or.inr (by rw [number]; omega)
  · exact Or.inl (by rw [number]; have beforeHeader:=rightImage.geometry.header_before_end; omega)

end InitECandidate.Solver.Input.CurrentVerify.FreshTransaction

#print axioms InitECandidate.Solver.Input.CurrentVerify.FreshTransaction.record_address_number
#print axioms InitECandidate.Solver.Input.CurrentVerify.FreshTransaction.record_addresses_distinct
#print axioms InitECandidate.Solver.Input.CurrentVerify.FreshTransaction.Context.after_persistent
#print axioms InitECandidate.Solver.Input.CurrentVerify.FreshTransaction.Context.of_erase
#print axioms InitECandidate.Solver.Input.CurrentVerify.FreshTransaction.Context.reset

#print axioms InitECandidate.Solver.Input.CurrentVerify.FreshTransaction.header_away_record
#print axioms InitECandidate.Solver.Input.CurrentVerify.FreshTransaction.Context.stored_table

#print axioms InitECandidate.Solver.Input.CurrentVerify.FreshTransaction.tail_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.FreshTransaction.body_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.FreshTransaction.specs_valid
#print axioms InitECandidate.Solver.Input.CurrentVerify.FreshTransaction.offsets_distinct
#print axioms InitECandidate.Solver.Input.CurrentVerify.FreshTransaction.first_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.FreshTransaction.body_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.FreshTransaction.Context.of_origin
#print axioms InitECandidate.Solver.Input.CurrentVerify.FreshTransaction.call_normal

namespace InitECandidate.Solver.Input.CurrentVerify.UncheckedSystem
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "process_unchecked_system_transaction")=some
      ([(ofString "target",.one),(ofString "data",.one),(ofString "data_n",.one)],body,.one) := by
  have found:=OriginalCode.indexed code installed 794
    (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_process_unchecked_system_transaction) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,
    Guest.Software.guestFn_process_unchecked_system_transaction,paramToHOL,shapeToHOL,List.map_cons,List.map_nil] using found

theorem after_fresh_shape : ∃ continuation,afterFresh=.decCall (ofString "code") (.comb [.one,.one])
    (ofString "ext_code_of") [QueryBranch.localVar "target"] continuation := by
  simp only [afterFresh,body,Guest.Software.guestFn_process_unchecked_system_transaction,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,QueryBranch.localVar]
  exact ⟨_,rfl⟩

/-- The same actual system-transaction prefix carries its complete normal
transaction-state images into ext_code_of. Callee locals are its own target/
data bindings; main's local environment is not an entry assumption. -/
theorem fresh_physical_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (record bs : BitVec 64)
    (runtime : CurrentStartup.ArenaState source)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word record)))
    (heapArena : AllocatedBytes.Arena record 0) (heapBound : record.toNat≤2952790016) (heapAligned : record.toNat%8=0)
    (blockState : source.globals.lookup (ofString "bs")=some (.val (.word bs)))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤75 ∨ ∃ current inner next,FreshTransaction.Context source current record bs next FreshTransaction.tables ∧
      current.globals.lookup (ofString "journal_n")=some (.val (.word 0#64)) ∧ current.locals=source.locals ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤75 ∧ CallPrefix.ScopeFrame post inner ∧
      evaluateHOLFiniteState current afterFresh=(outcome,inner) := by
  rcases fresh_trace source post runtime.code outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨current,inner,execution,forward,price,scope,continued⟩:=reached
    change CallPrefix.Execution source [.command (.call (some (none,none)) (ofString "state_fresh_tx") [])] current at execution
    have callRun : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "state_fresh_tx") [])=(none,current):=by
      have actual:=execution.singleton
      cases actual with | command _ _ run=>exact run
    obtain ⟨next,physical,counter,locals⟩:=FreshTransaction.call_normal source current record bs runtime heapCell heapArena heapBound heapAligned blockState callRun
    exact Or.inr ⟨current,inner,next,physical,counter,locals,forward,price,scope,continued⟩

/-- The current initialized-state context supplies the genuine fresh
transaction's heap and typed block-state global. Its values are derived
from the actual earlier state initialization and retained main prefix. -/
theorem fresh_records_trace {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {frontier ws bs : BitVec 64}
    (records : Mpt.StateInit.MemoryContext source frontier ws bs)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤75 ∨ ∃ record current inner next,
      source.globals.lookup (ofString "heap_ptr")=some (.val (.word record)) ∧
      FreshTransaction.Context source current record bs next FreshTransaction.tables ∧
      current.globals.lookup (ofString "journal_n")=some (.val (.word 0#64)) ∧ current.locals=source.locals ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤75 ∧ CallPrefix.ScopeFrame post inner ∧
      evaluateHOLFiniteState current afterFresh=(outcome,inner) := by
  obtain ⟨record,cell,arena,bounded,aligned,afterFrontier⟩:=records.heap
  rcases fresh_physical_trace source post record bs records.arena cell arena bounded aligned records.bsCell outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨current,inner,next,physical,counter,locals,forward,price,scope,continued⟩:=reached
    exact Or.inr ⟨record,current,inner,next,cell,physical,counter,locals,forward,price,scope,continued⟩

end InitECandidate.Solver.Input.CurrentVerify.UncheckedSystem

#print axioms InitECandidate.Solver.Input.CurrentVerify.UncheckedSystem.original_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.UncheckedSystem.after_fresh_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.UncheckedSystem.fresh_physical_trace

#print axioms InitECandidate.Solver.Input.CurrentVerify.UncheckedSystem.fresh_records_trace

namespace InitECandidate.Solver.Input.CurrentVerify.AccountAccess
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000

def body : ProgHOL 64:=match Guest.Software.guestFn_get_account_optional with | .function fn=>progToHOL fn.body | _=>.skip
def arguments : List (ExpHOL 64):=[.load .one (FreshTransaction.field 8),localVar "addr",.const 1#64]
def caller : ProgHOL 64:=.call (some (none,none)) (ofString "htab_set") arguments
def afterSet : ProgHOL 64:=match body with | .seq _ rest=>rest | _=>.skip

theorem body_shape : body=.seq caller afterSet := by
  simp only [body,Guest.Software.guestFn_get_account_optional,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    caller,arguments,afterSet,FreshTransaction.field,Scalar.plus,localVar,Option.map_none]

theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "get_account_optional")=some ([(ofString "addr",.one)],body,.one) := by
  have found:=OriginalCode.indexed code installed 340
    (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_get_account_optional) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,
    Guest.Software.guestFn_get_account_optional,paramToHOL,shapeToHOL,List.map_cons,List.map_nil] using found

/-- Actual first access-table state retained for the pre-state call.
Location and separation come from the same fresh-table allocation history. -/
structure AccessState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record access : BitVec 64) : Prop where
  field : source.memory (record+8#64)=.word access
  single : CurrentTable.New.ScalarSingle source access 20#64 64#64 1#64 1#64
  afterRecord : record.toNat+72≤access.toNat
  separated : FreshTransaction.Separated source record FreshTransaction.tables

theorem AccessState.of_erase {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {record access : BitVec 64}
    (state : AccessState source record access) (same : LocalEffects.erase target=LocalEffects.erase source) : AccessState target record access := by
  have memory:=LocalEffects.memory_of_erase source target same
  exact ⟨(congrFun memory (record+8#64)).trans state.field,state.single.of_erase same,state.afterRecord,
    state.separated.of_memory (by intro spec member; exact congrFun memory _)⟩

/-- The original actual scalar ABI retains the same physical transaction
context at the callee entry, with that callee's own address binding. -/
theorem call_entry {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {record bs heap : BitVec 64}
    (context : FreshTransaction.Context origin source record bs heap FreshTransaction.tables) (pointer : BitVec 64) :
    ∃ callee,lookupCodeHOLFinite source.code.lookup (ofString "get_account_optional") [.val (.word pointer)]=some (body,callee,.one) ∧
      callee.lookup (ofString "addr")=some (.val (.word pointer)) ∧
      FreshTransaction.Context origin (callEntryStateHOLFinite source callee) record bs heap FreshTransaction.tables := by
  obtain ⟨callee,called,cell⟩:=word_environment source.code.lookup (ofString "get_account_optional") (ofString "addr") body .one pointer
    (original_code source.code context.runtime.code)
  exact ⟨callee,called,cell,context.of_erase rfl⟩

/-- The same actual fresh transaction supplies its original access table
and its20byte key width at get_account_optional's first real call. No
initialized key byte or successful insertion is an entry assumption. -/
theorem first_set_entry {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {record bs heap pointer : BitVec 64}
    (context : FreshTransaction.Context origin source record bs heap FreshTransaction.tables)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word pointer))) :
    ∃ table,source.memory (record+8#64)=.word table ∧ CurrentTable.New.ScalarEmpty source table 20#64 64#64 ∧
      record.toNat+72≤table.toNat ∧
      evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
        some [.val (.word table),.val (.word pointer),.val (.word 1#64)] := by
  obtain ⟨table,field,image,afterRecord,beforeHeap,endBeforeHeap⟩:=context.images FreshTransaction.firstTable (by simp [FreshTransaction.tables])
  change source.memory (record+8#64)=.word table at field
  change CurrentTable.New.ScalarEmpty source table 20#64 64#64 at image
  have tsRead : eval source (.var .global (ofString "ts"))=some (.val (.word record)):=by
    simp [eval,evalHOLExact,toExact,context.recordCell]
  have addressRead:=Scalar.plus_read source (.var .global (ofString "ts")) record 8 tsRead
  have tableRead:=Witness.load_word_read source (FreshTransaction.field 8) (record+8#64) table addressRead
    (AllocatedBytes.word_mapped source record 72 8 context.runtime.domain context.recordArena (by decide) context.recordAligned (by decide)) field
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some [.val (.word table),.val (.word pointer),.val (.word 1#64)]:=by
    simp only [eval] at tableRead
    simp only [arguments,evalListHOLFinite,evalListHOLExact,tableRead]
    simp [evalHOLExact,localVar,addressCell]
  exact ⟨table,field,image,afterRecord,args⟩

theorem first_set_cost {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {record bs heap pointer : BitVec 64}
    (context : FreshTransaction.Context origin source record bs heap FreshTransaction.tables)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word pointer))) :
    source.clock-(evaluateHOLFiniteState source caller).2.clock≤29 := by
  obtain ⟨table,field,image,afterRecord,args⟩:=first_set_entry context addressCell
  exact CurrentTable.Set.account_first_call_cost source table 64#64 pointer 1#64 image context.runtime.code arguments args

/-- A real successful first access insertion retains every other fresh
transaction table and the earlier persistent state. The modified access
image is excluded from the remaining empty-table context. -/
theorem first_set_normal {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory} {record bs heap pointer : BitVec 64}
    (context : FreshTransaction.Context origin source record bs heap FreshTransaction.tables)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word pointer)))
    (normal : evaluateHOLFiniteState source caller=(none,post)) :
    ∃ access,source.memory (record+8#64)=.word access ∧ post.memory (record+8#64)=.word access ∧
      CurrentTable.New.ScalarFrame source post access 20#64 64#64 ∧
      FreshTransaction.Context origin post record bs heap FreshTransaction.remainingTables ∧
      FreshTransaction.Separated post record FreshTransaction.tables ∧ post.locals=source.locals ∧
      AccessState post record access := by
  obtain ⟨access,accessCell,accessImage,accessAfterRecord,args⟩:=first_set_entry context addressCell
  obtain ⟨frame,locals,single⟩:=CurrentTable.Set.scalar_empty_call_frame accessImage context.runtime.code arguments args (by decide) (by decide) normal
  have globals:=congrArg PanSemStateFiniteExact.globals frame.fields
  change post.globals=source.globals at globals
  have domain:=MemoryMetadata.domain frame.fields
  have code:=MemoryMetadata.code frame.fields
  have runtime : CurrentStartup.ArenaState post:=
    ⟨by rw [globals]; exact context.runtime.scratch,by rw [globals]; exact context.runtime.frame,domain.trans context.runtime.domain,
      by rw [code]; exact context.runtime.code⟩
  have recordMemory (spec : FreshTransaction.TableSpec) (member : spec∈FreshTransaction.tables) :
      post.memory (record+BitVec.ofNat 64 spec.offset)=source.memory (record+BitVec.ofNat 64 spec.offset):=by
    apply frame.memory
    apply Or.inl
    rw [FreshTransaction.record_address_number record context.recordArena spec.offset (context.valid spec member).2.1]
    have inside:=(context.valid spec member).2.1
    omega
  have oldFrame : PersistentMemoryFrame source post record:=by
    refine ⟨⟨heap,by rw [globals]; exact context.heapCell,context.heapArena,context.heapBound,context.heapAligned,by have before:=context.afterRecord; omega⟩,?_,?_⟩
    · rw [←globals]
      exact frame.fields
    · intro query before
      exact frame.memory query (Or.inl (by omega))
  have older:=context.older.trans origin source post record record oldFrame (Nat.le_refl _)
  have separated:=context.separated.of_memory recordMemory
  have images : FreshTransaction.Images post record heap FreshTransaction.remainingTables:=by
    intro spec member
    have fullMember : spec∈FreshTransaction.tables:=List.mem_cons_of_mem FreshTransaction.firstTable member
    obtain ⟨table,pointer,image,afterRecord,beforeHeap,endBeforeHeap⟩:=context.images spec fullMember
    have different : FreshTransaction.firstTable.offset≠spec.offset:=by
      intro same
      exact (List.nodup_cons.mp FreshTransaction.offsets_distinct).1 (List.mem_map.mpr ⟨spec,member,same.symm⟩)
    have split:=context.tables_separated FreshTransaction.firstTable spec (by simp [FreshTransaction.tables]) fullMember different access table accessCell pointer
    dsimp only [FreshTransaction.firstTable] at split
    have currentImage : CurrentTable.New.ScalarEmpty post table spec.key spec.cap:=by
      apply image.of_memory domain
      intro entry entryMember
      apply frame.memory
      have lower:=CurrentTable.New.scalar_write_lower table spec.key spec.cap entry image.geometry.table entryMember
      have upper:=CurrentTable.New.scalar_write_before table spec.key spec.cap entry image.geometry.table entryMember
      rcases split with before|after
      · exact Or.inr (by omega)
      · exact Or.inl (by have endBefore:=image.geometry.header_before_end; omega)
    exact ⟨table,(recordMemory spec fullMember).trans pointer,currentImage,afterRecord,beforeHeap,endBeforeHeap⟩
  have current : FreshTransaction.Context origin post record bs heap FreshTransaction.remainingTables:=by
    refine ⟨runtime,by rw [globals]; exact context.recordCell,context.recordArena,context.recordAligned,
      by rw [globals]; exact context.heapCell,context.heapArena,context.heapBound,context.heapAligned,context.afterRecord,?_,?_,images,older,?_,?_⟩
    · exact (frame.memory record (Or.inl (by omega))).trans context.blockField
    · intro spec member
      exact context.valid spec (List.mem_cons_of_mem FreshTransaction.firstTable member)
    · intro name notHeap notRecord notCounter
      rw [globals]
      exact context.globals name notHeap notRecord notCounter
    · intro left lm right rm different
      exact separated left (List.mem_cons_of_mem FreshTransaction.firstTable lm) right (List.mem_cons_of_mem FreshTransaction.firstTable rm) different
  have accessStored : post.memory (record+8#64)=.word access:=
    (recordMemory FreshTransaction.firstTable (by simp [FreshTransaction.tables])).trans accessCell
  exact ⟨access,accessCell,accessStored,frame,current,separated,locals,⟨accessStored,single,accessAfterRecord,separated⟩⟩

def getArguments : List (ExpHOL 64):=[.load .one (FreshTransaction.field 16),localVar "addr"]
def afterGet : ProgHOL 64:=match afterSet with | .decCall _ _ _ _ rest=>rest | _=>.skip
def missGuard : ProgHOL 64:=.ite (.cmp .notEqual (.rfield 0 (localVar "w")) (.const 0#64)) (.return (.rfield 1 (localVar "w"))) .skip
def afterMiss : ProgHOL 64:=match afterGet with | .seq _ rest=>rest | _=>.skip

theorem getter_shape : afterSet=.decCall (ofString "w") CurrentTable.Get.resultShape (ofString "htab_get") getArguments afterGet := by
  simp only [afterSet,afterGet,body,Guest.Software.guestFn_get_account_optional,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    getArguments,FreshTransaction.field,Scalar.plus,localVar,CurrentTable.Get.resultShape,Option.map_none]

theorem miss_shapes : afterGet=.seq missGuard afterMiss ∧
    afterMiss=.decCall (ofString "a") .one (ofString "get_pre_state_account_optional") [localVar "addr"] (.return (localVar "a")) := by
  simp only [afterMiss,afterGet,afterSet,body,Guest.Software.guestFn_get_account_optional,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    missGuard,localVar,Option.map_none]
  trivial

theorem absent_after_get (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (cell : source.locals.lookup (ofString "w")=some CurrentTable.Get.absentValue) :
    evaluateHOLFiniteState source afterGet=evaluateHOLFiniteState source afterMiss := by
  have read : eval source (.cmp .notEqual (.rfield 0 (localVar "w")) (.const 0#64))=some (.val (.word 0#64)):=by
    simp [eval,evalHOLExact,toExact,localVar,cell,CurrentTable.Get.absentValue,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have skipped : evaluateHOLFiniteState source missGuard=(none,source):=by
    simp only [eval] at read
    rw [missGuard,evaluateHOLFiniteState_ite,read]
    simp [evaluateHOLFiniteState_skip]
  rw [miss_shapes.1,evaluateHOLFiniteState_seq_line780,skipped]

theorem cache_get_entry {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {record bs heap pointer : BitVec 64}
    (context : FreshTransaction.Context origin source record bs heap FreshTransaction.remainingTables)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word pointer))) :
    ∃ table,CurrentTable.New.ScalarEmpty source table 20#64 64#64 ∧
      evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) getArguments=
        some [.val (.word table),.val (.word pointer)] := by
  obtain ⟨table,field,image,afterRecord,beforeHeap,endBeforeHeap⟩:=context.images ⟨20#64,64#64,16⟩ (by simp [FreshTransaction.remainingTables])
  change source.memory (record+16#64)=.word table at field
  have tsRead : eval source (.var .global (ofString "ts"))=some (.val (.word record)):=by
    simp [eval,evalHOLExact,context.recordCell]
  have addressRead:=Scalar.plus_read source (.var .global (ofString "ts")) record 16 tsRead
  have tableRead:=Witness.load_word_read source (FreshTransaction.field 16) (record+16#64) table addressRead
    (AllocatedBytes.word_mapped source record 72 16 context.runtime.domain context.recordArena (by decide) context.recordAligned (by decide)) field
  refine ⟨table,image,?_⟩
  simp only [eval] at tableRead
  simp only [getArguments,evalListHOLFinite,evalListHOLExact,tableRead]
  simp [evalHOLExact,localVar,addressCell]

/-- The actual original account helper either stops within31source ticks
or reaches its real pre-state call after the first access insertion and
actual absent cache result. All untouched fresh tables and earlier state
are retained from these same executions. -/
theorem to_pre_state {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory} {record bs heap pointer : BitVec 64}
    (context : FreshTransaction.Context origin source record bs heap FreshTransaction.tables)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word pointer)))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    (source.clock-post.clock≤31 ∧ ∀ value,outcome≠some (.returned value)) ∨
      ∃ current inner,FreshTransaction.Context origin current record bs heap FreshTransaction.remainingTables ∧
        current.locals.lookup (ofString "addr")=some (.val (.word pointer)) ∧ current.clock≤source.clock ∧
        source.clock-current.clock≤31 ∧ CallPrefix.ScopeFrame post inner ∧ evaluateHOLFiniteState current afterMiss=(outcome,inner) ∧
        ∃ access,AccessState current record access := by
  rw [body_shape] at run
  let actions : List CallPrefix.Action:=[.command caller]
  change evaluateHOLFiniteState source (CallPrefix.program actions afterSet)=(outcome,post) at run
  have priced : source.clock-(evaluateHOLFiniteState source (CallPrefix.program actions .skip)).2.clock≤29:=by
    simpa only [actions,CallPrefix.program,Nat.add_zero] using ClockCost.sequence_current source caller .skip 29 0 (first_set_cost context addressCell) (ClockCost.skip source.code)
  rcases CallPrefix.priced_frame_trace source post actions afterSet 29 priced outcome run with stopped|reached
  · refine Or.inl ⟨by have bound:=stopped.1; omega,?_⟩
    intro value returned
    have safe : LocalPrefix (ofString "addr") (CallPrefix.program actions .skip):=.seq (.call none _ _ (by simp)) .skip
    apply (safe.summary_full source).2.1 value
    rw [←stopped.2]
    exact returned
  · obtain ⟨entered,outer,execution,forward,price,scope,continued⟩:=reached
    have callerRun : evaluateHOLFiniteState source caller=(none,entered):=by
      have actual:=execution.singleton
      cases actual with | command _ _ normal=>exact normal
    obtain ⟨access,accessCell,accessStored,accessFrame,remaining,separated,locals,accessState⟩:=first_set_normal context addressCell callerRun
    have enteredAddress : entered.locals.lookup (ofString "addr")=some (.val (.word pointer)):=by rw [locals]; exact addressCell
    obtain ⟨cache,image,args⟩:=cache_get_entry remaining enteredAddress
    rw [getter_shape] at continued
    rcases CurrentTable.Get.scoped_scalar_empty_trace entered outer cache 20#64 64#64 pointer image remaining.runtime.code "w" getArguments afterGet args outcome continued with stopped|reached
    · exact Or.inl ⟨by rw [scope.clock]; have bound:=stopped.1; omega,stopped.2⟩
    · obtain ⟨target,inner,frame,getForward,getPrice,continued,endpoint⟩:=reached
      let current:=CallNormal.continuationEntry entered target "w" CurrentTable.Get.absentValue
      change evaluateHOLFiniteState current afterGet=(outcome,inner) at continued
      rw [absent_after_get current (CallNormal.continuation_lookup_same entered target "w" CurrentTable.Get.absentValue)] at continued
      have retained : FreshTransaction.Context origin current record bs heap FreshTransaction.remainingTables:=remaining.of_erase frame
      have currentAddress : current.locals.lookup (ofString "addr")=some (.val (.word pointer)):=
        (CallNormal.continuation_lookup_other entered target "w" "addr" CurrentTable.Get.absentValue (by decide)).trans enteredAddress
      have currentClock : current.clock=target.clock:=rfl
      have lastScope : CallPrefix.ScopeFrame outer inner:=by rw [endpoint]; exact ⟨rfl,rfl⟩
      exact Or.inr ⟨current,inner,retained,currentAddress,by omega,by omega,scope.trans lastScope,continued,access,accessState.of_erase frame⟩

end InitECandidate.Solver.Input.CurrentVerify.AccountAccess

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountAccess.body_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountAccess.first_set_cost

#print axioms InitECandidate.Solver.Input.CurrentVerify.FreshTransaction.Separated.of_memory
#print axioms InitECandidate.Solver.Input.CurrentVerify.FreshTransaction.Context.tables_separated

#print axioms InitECandidate.Solver.Input.CurrentVerify.FreshTransaction.Context.other_header_outside

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountAccess.first_set_entry
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountAccess.first_set_normal

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountAccess.getter_shape

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountAccess.miss_shapes

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountAccess.absent_after_get

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountAccess.cache_get_entry

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountAccess.to_pre_state

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountAccess.original_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountAccess.call_entry

namespace InitECandidate.Solver.Input.CurrentVerify.FreshTransaction
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The same actual fresh-state return also retains the initialized MPT
records and their earlier contents for account/code access after this prefix. -/
theorem Context.retained_records {source current origin : PanSemStateFiniteExact 64 Guest.HostMemory}
    {record bs heap cutoff ws : BitVec 64} {done : List TableSpec}
    (context : Context source current record bs heap done)
    (records : RunAttempt.RetainedRecords origin source cutoff ws bs) (before : cutoff.toNat≤record.toNat) :
    RunAttempt.RetainedRecords origin current cutoff ws bs := by
  have floor : NormalHeapEffects.AtLeast cutoff.toNat current:=
    ⟨heap,context.heapCell,by have room:=context.afterRecord; omega,context.heapBound,context.heapAligned⟩
  apply records.after context.runtime floor
    (context.globals _ (by decide) (by decide) (by decide)) (context.globals _ (by decide) (by decide) (by decide))
  intro query above below
  exact context.older.memory query (Nat.lt_of_lt_of_le below before)

/-- The completed block-state snapshot survives the same actual fresh-state
and access-setter memory frames as its earlier physical record context. -/
theorem Context.initialized_records {source current origin : PanSemStateFiniteExact 64 Guest.HostMemory}
    {record bs heap cutoff ws : BitVec 64} {done : List TableSpec}
    (context : Context source current record bs heap done)
    (records : RunAttempt.InitializedRecords origin source cutoff ws bs) (before : cutoff.toNat≤record.toNat) :
    RunAttempt.InitializedRecords origin current cutoff ws bs :=
  records.with_records (context.retained_records records.toRetainedRecords before)

end InitECandidate.Solver.Input.CurrentVerify.FreshTransaction

#print axioms InitECandidate.Solver.Input.CurrentVerify.FreshTransaction.Context.retained_records

namespace InitECandidate.Solver.Input.CurrentVerify.UncheckedSystem
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- These are the literal arguments of execute_block's first system call. -/
def firstArguments : List (ExpHOL 64):=[.var .global (ofString "beacon_roots_address"),.load .one (Scalar.plus (localVar "si") 24),.const 32#64]
def firstCall : ProgHOL 64:=.call (some (none,none)) (ofString "process_unchecked_system_transaction") firstArguments
def firstContinuation : ProgHOL 64:=match ExecuteBlock.beforeFirstSystem with | .seq _ rest=>rest | _=>.skip

theorem first_shape : ExecuteBlock.beforeFirstSystem=.seq firstCall firstContinuation := by
  simp only [ExecuteBlock.beforeFirstSystem,ExecuteBlock.body,Guest.Software.guestFn_execute_block,progToHOL,CallPrefix.cutAt,
    expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,firstCall,firstArguments,firstContinuation,Scalar.plus,localVar]

/-- Derive this genuine call's scalar ABI and initialized state from its
actual argument evaluation/code lookup and already retained main inputs.
Neither a typed address global nor a future successful callee is assumed. -/
theorem first_entry {input : Guest.InputBlob} {source origin : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header ws bs : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (records : RunAttempt.RetainedRecords origin source header ws bs)
    (values : List (ValueHOL 64)) (actual : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) firstArguments=some values)
    (called : lookupCodeHOLFinite source.code.lookup (ofString "process_unchecked_system_transaction") values=some (actual,callee,shape)) :
    ∃ target,eval source (.var .global (ofString "beacon_roots_address"))=some (.val (.word target)) ∧
      values=[.val (.word target),.val (.word (pointer+26#64)),.val (.word 32#64)] ∧ actual=body ∧ shape=.one ∧
      callee.lookup (ofString "target")=some (.val (.word target)) ∧ callee.lookup (ofString "data")=some (.val (.word (pointer+26#64))) ∧
      callee.lookup (ofString "data_n")=some (.val (.word 32#64)) ∧
      Mpt.StateInit.MemoryContext (callEntryStateHOLFinite source callee) ws ws bs := by
  have siRead : eval source (localVar "si")=some (.val (.word si)):=by simp [eval,evalHOLExact,toExact,localVar,data.siLocal]
  have parentRead : eval source (.load .one (Scalar.plus (localVar "si") 24))=some (.val (.word (pointer+26#64))):=
    Witness.load_word_read source _ (si+24#64) (pointer+26#64) (Scalar.plus_read source (localVar "si") si 24 siRead)
      (AllocatedBytes.word_mapped source si 96 24 data.arena.domain data.siArena (by decide) data.siAligned (by decide)) data.parentCell
  cases targetRead : eval source (.var .global (ofString "beacon_roots_address")) with
  | none=>
    simp only [eval] at targetRead parentRead
    simp [firstArguments,evalListHOLFinite,evalListHOLExact,targetRead,parentRead] at args
  | some targetValue=>
    have expectedArgs : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) firstArguments=
        some [targetValue,.val (.word (pointer+26#64)),.val (.word 32#64)]:=by
      simp only [eval] at targetRead parentRead
      simp only [firstArguments,evalListHOLFinite,evalListHOLExact,targetRead,parentRead]
      rfl
    have sameValues : values=[targetValue,.val (.word (pointer+26#64)),.val (.word 32#64)]:=Option.some.inj (args.symm.trans expectedArgs)
    subst values
    obtain ⟨target,left,middle,targetEq,dataEq,lengthEq⟩:=CallNormal.three_scalar_words source.code.lookup
      (ofString "process_unchecked_system_transaction") (ofString "target") (ofString "data") (ofString "data_n") body actual .one shape
      (original_code source.code data.arena.code) targetValue (.val (.word (pointer+26#64))) (.val (.word 32#64)) callee called
    rw [targetEq] at called
    obtain ⟨expected,lookup,targetCell,dataCell,lengthCell⟩:=word_triple_environment source.code.lookup
      (ofString "process_unchecked_system_transaction") (ofString "target") (ofString "data") (ofString "data_n") body .one target (pointer+26#64) 32#64
      (by decide) (by decide) (by decide) (original_code source.code data.arena.code)
    have sameCall:=Option.some.inj (called.symm.trans lookup)
    have bodyEq : actual=body:=congrArg Prod.fst sameCall
    have calleeEq : callee=expected:=congrArg (fun result : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>result.2.1) sameCall
    have shapeEq : shape=.one:=congrArg (fun result : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>result.2.2) sameCall
    refine ⟨target,?_,?_,bodyEq,shapeEq,?_,?_,?_,records.context.of_frame rfl⟩
    · simpa only [targetEq] using targetRead
    · rw [targetEq]
    · rw [calleeEq]; exact targetCell
    · rw [calleeEq]; exact dataCell
    · rw [calleeEq]; exact lengthCell

/-- The real first system caller reaches ext_code_of with the fresh physical
transaction state and original target/data words, or stops within76 caller
source ticks. The fresh state's bounds come from the same actual execution. -/
theorem first_fresh_trace {input : Guest.InputBlob} {source origin post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header ws bs : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (records : RunAttempt.RetainedRecords origin source header ws bs)
    (afterHeader : NormalHeapEffects.AtLeast header.toNat source)
    (values : List (ValueHOL 64)) (actual : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) firstArguments=some values)
    (called : lookupCodeHOLFinite source.code.lookup (ofString "process_unchecked_system_transaction") values=some (actual,callee,shape))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) actual=(outcome,post)) :
    source.clock-post.clock≤76 ∨ ∃ target tx current inner next,
      callee.lookup (ofString "target")=some (.val (.word target)) ∧
      FreshTransaction.Context (callEntryStateHOLFinite source callee) current tx bs next FreshTransaction.tables ∧
      RunAttempt.RetainedRecords origin current header ws bs ∧
      current.globals.lookup (ofString "journal_n")=some (.val (.word 0#64)) ∧
      current.locals.lookup (ofString "target")=some (.val (.word target)) ∧
      current.locals.lookup (ofString "data")=some (.val (.word (pointer+26#64))) ∧ current.locals.lookup (ofString "data_n")=some (.val (.word 32#64)) ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤76 ∧ CallPrefix.ScopeFrame post inner ∧ evaluateHOLFiniteState current afterFresh=(outcome,inner) := by
  obtain ⟨target,targetRead,valuesEq,bodyEq,shapeEq,targetCell,dataCell,lengthCell,context⟩:=first_entry data records values actual callee shape args called
  rw [bodyEq] at run
  rcases fresh_records_trace context outcome run with stopped|reached
  · exact Or.inl (by change source.clock-1-post.clock≤75 at stopped; omega)
  · obtain ⟨tx,current,inner,next,txCell,physical,counter,locals,forward,price,scope,continued⟩:=reached
    change current.clock≤source.clock-1 at forward
    change source.clock-1-current.clock≤75 at price
    obtain ⟨old,oldCell,lower,upper,aligned⟩:=afterHeader
    have same : old=tx:=by simpa only [ValueHOL.val.injEq,HolWordLab.word.injEq] using Option.some.inj (oldCell.symm.trans txCell)
    have beforeTx : header.toNat≤tx.toNat:=by rw [←same]; exact lower
    have retained:=physical.retained_records (records.of_erase rfl) beforeTx
    refine Or.inr ⟨target,tx,current,inner,next,targetCell,physical,retained,counter,?_,?_,?_,by omega,by omega,scope,continued⟩
    · rw [locals]; exact targetCell
    · rw [locals]; exact dataCell
    · rw [locals]; exact lengthCell

end InitECandidate.Solver.Input.CurrentVerify.UncheckedSystem

#print axioms InitECandidate.Solver.Input.CurrentVerify.UncheckedSystem.first_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.UncheckedSystem.first_entry
#print axioms InitECandidate.Solver.Input.CurrentVerify.UncheckedSystem.first_fresh_trace

namespace InitECandidate.Solver.Input.CurrentVerify.PreStateAccount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000

def body : ProgHOL 64:=match Guest.Software.guestFn_get_pre_state_account_optional with | .function fn=>progToHOL fn.body | _=>.skip
def afterSet : ProgHOL 64:=match body with | .seq _ rest=>rest | _=>.skip

theorem body_shape : body=.seq AccountAccess.caller afterSet := by
  simp only [body,afterSet,Guest.Software.guestFn_get_pre_state_account_optional,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    AccountAccess.caller,AccountAccess.arguments,FreshTransaction.field,Scalar.plus,localVar,Option.map_none]

theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "get_pre_state_account_optional")=some ([(ofString "addr",.one)],body,.one) := by
  have found:=OriginalCode.indexed code installed 338
    (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_get_pre_state_account_optional) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,
    Guest.Software.guestFn_get_pre_state_account_optional,paramToHOL,shapeToHOL,List.map_cons,List.map_nil] using found

/-- The genuine pre-state ABI carries the first access insertion's actual
singleton and every remaining fresh table into the same called body. -/
theorem call_entry {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {record bs heap access : BitVec 64}
    (context : FreshTransaction.Context origin source record bs heap FreshTransaction.remainingTables)
    (field : source.memory (record+8#64)=.word access)
    (single : CurrentTable.New.ScalarSingle source access 20#64 64#64 1#64 1#64) (pointer : BitVec 64) :
    ∃ callee,lookupCodeHOLFinite source.code.lookup (ofString "get_pre_state_account_optional") [.val (.word pointer)]=some (body,callee,.one) ∧
      callee.lookup (ofString "addr")=some (.val (.word pointer)) ∧
      FreshTransaction.Context origin (callEntryStateHOLFinite source callee) record bs heap FreshTransaction.remainingTables ∧
      (callEntryStateHOLFinite source callee).memory (record+8#64)=.word access ∧
      CurrentTable.New.ScalarSingle (callEntryStateHOLFinite source callee) access 20#64 64#64 1#64 1#64 := by
  obtain ⟨callee,called,cell⟩:=word_environment source.code.lookup (ofString "get_pre_state_account_optional") (ofString "addr") body .one pointer
    (original_code source.code context.runtime.code)
  exact ⟨callee,called,cell,context.of_erase rfl,field,single.of_erase rfl⟩

/-- The exact repeated access insertion at the start of the original
pre-state helper costs295 caller ticks on every outcome, from its retained
real singleton and transaction record. Query contents are unrestricted. -/
theorem first_set_cost {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {record bs heap access pointer : BitVec 64}
    (context : FreshTransaction.Context origin source record bs heap FreshTransaction.remainingTables)
    (field : source.memory (record+8#64)=.word access)
    (single : CurrentTable.New.ScalarSingle source access 20#64 64#64 1#64 1#64)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word pointer))) :
    source.clock-(evaluateHOLFiniteState source AccountAccess.caller).2.clock≤295 := by
  have tsRead : eval source (.var .global (ofString "ts"))=some (.val (.word record)):=by
    simp [eval,evalHOLExact,toExact,context.recordCell]
  have addressRead:=Scalar.plus_read source (.var .global (ofString "ts")) record 8 tsRead
  have tableRead:=Witness.load_word_read source (FreshTransaction.field 8) (record+8#64) access addressRead
    (AllocatedBytes.word_mapped source record 72 8 context.runtime.domain context.recordArena (by decide) context.recordAligned (by decide)) field
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) AccountAccess.arguments=
      some [.val (.word access),.val (.word pointer),.val (.word 1#64)]:=by
    simp only [eval] at tableRead
    simp only [AccountAccess.arguments,evalListHOLFinite,evalListHOLExact,tableRead]
    simp [evalHOLExact,localVar,addressCell]
  exact CurrentTable.Set.account_second_call_cost source access 64#64 pointer 1#64 1#64 single (by decide) context.runtime.code AccountAccess.arguments args

end InitECandidate.Solver.Input.CurrentVerify.PreStateAccount

#print axioms InitECandidate.Solver.Input.CurrentVerify.PreStateAccount.body_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.PreStateAccount.original_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.PreStateAccount.call_entry
#print axioms InitECandidate.Solver.Input.CurrentVerify.PreStateAccount.first_set_cost

namespace InitECandidate.Solver.Input.CurrentVerify.PreStateAccount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The same original callee receives the derived allocation ordering and
full table separation as well as the actual first-insertion singleton. -/
theorem call_entry_context {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {record bs heap access : BitVec 64}
    (context : FreshTransaction.Context origin source record bs heap FreshTransaction.remainingTables)
    (state : AccountAccess.AccessState source record access) (pointer : BitVec 64) :
    ∃ callee,lookupCodeHOLFinite source.code.lookup (ofString "get_pre_state_account_optional") [.val (.word pointer)]=some (body,callee,.one) ∧
      callee.lookup (ofString "addr")=some (.val (.word pointer)) ∧
      FreshTransaction.Context origin (callEntryStateHOLFinite source callee) record bs heap FreshTransaction.remainingTables ∧
      AccountAccess.AccessState (callEntryStateHOLFinite source callee) record access := by
  obtain ⟨callee,called,cell,retained,field,single⟩:=call_entry context state.field state.single pointer
  exact ⟨callee,called,cell,retained,state.of_erase rfl⟩

/-- A real successful repeated access insertion preserves every remaining
fresh table, the transaction record and all earlier persistent state. The
modified access table is allowed to contain the actual second insertion. -/
theorem first_set_normal {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory} {record bs heap access pointer : BitVec 64}
    (context : FreshTransaction.Context origin source record bs heap FreshTransaction.remainingTables)
    (state : AccountAccess.AccessState source record access)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word pointer)))
    (normal : evaluateHOLFiniteState source AccountAccess.caller=(none,post)) :
    CurrentTable.New.ScalarFrame source post access 20#64 64#64 ∧
      FreshTransaction.Context origin post record bs heap FreshTransaction.remainingTables ∧
      post.memory (record+8#64)=.word access ∧ FreshTransaction.Separated post record FreshTransaction.tables ∧ post.locals=source.locals := by
  have tsRead : eval source (.var .global (ofString "ts"))=some (.val (.word record)):=by
    simp [eval,evalHOLExact,toExact,context.recordCell]
  have addressRead:=Scalar.plus_read source (.var .global (ofString "ts")) record 8 tsRead
  have tableRead:=Witness.load_word_read source (FreshTransaction.field 8) (record+8#64) access addressRead
    (AllocatedBytes.word_mapped source record 72 8 context.runtime.domain context.recordArena (by decide) context.recordAligned (by decide)) state.field
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) AccountAccess.arguments=
      some [.val (.word access),.val (.word pointer),.val (.word 1#64)]:=by
    simp only [eval] at tableRead
    simp only [AccountAccess.arguments,evalListHOLFinite,evalListHOLExact,tableRead]
    simp [evalHOLExact,localVar,addressCell]
  obtain ⟨frame,locals⟩:=CurrentTable.Set.scalar_single_call_frame state.single (by decide) context.runtime.code AccountAccess.arguments args normal
  have globals:=congrArg PanSemStateFiniteExact.globals frame.fields
  change post.globals=source.globals at globals
  have domain:=MemoryMetadata.domain frame.fields
  have code:=MemoryMetadata.code frame.fields
  have runtime : CurrentStartup.ArenaState post:=
    ⟨by rw [globals]; exact context.runtime.scratch,by rw [globals]; exact context.runtime.frame,domain.trans context.runtime.domain,
      by rw [code]; exact context.runtime.code⟩
  have recordMemory (spec : FreshTransaction.TableSpec) (member : spec∈FreshTransaction.tables) :
      post.memory (record+BitVec.ofNat 64 spec.offset)=source.memory (record+BitVec.ofNat 64 spec.offset):=by
    apply frame.memory
    apply Or.inl
    rw [FreshTransaction.record_address_number record context.recordArena spec.offset (FreshTransaction.specs_valid spec member).2.1]
    have inside:=(FreshTransaction.specs_valid spec member).2.1
    have before:=state.afterRecord
    omega
  have oldFrame : PersistentMemoryFrame source post record:=by
    refine ⟨⟨heap,by rw [globals]; exact context.heapCell,context.heapArena,context.heapBound,context.heapAligned,by have before:=context.afterRecord; omega⟩,?_,?_⟩
    · rw [←globals]
      exact frame.fields
    · intro query before
      exact frame.memory query (Or.inl (by have lower:=state.afterRecord; omega))
  have older:=context.older.trans origin source post record record oldFrame (Nat.le_refl _)
  have separated:=state.separated.of_memory recordMemory
  have images : FreshTransaction.Images post record heap FreshTransaction.remainingTables:=by
    intro spec member
    have fullMember : spec∈FreshTransaction.tables:=List.mem_cons_of_mem FreshTransaction.firstTable member
    obtain ⟨table,pointer,image,afterRecord,beforeHeap,endBeforeHeap⟩:=context.images spec member
    have different : FreshTransaction.firstTable.offset≠spec.offset:=by
      intro same
      exact (List.nodup_cons.mp FreshTransaction.offsets_distinct).1 (List.mem_map.mpr ⟨spec,member,same.symm⟩)
    obtain ⟨left,right,lc,rc,split⟩:=state.separated FreshTransaction.firstTable (by simp [FreshTransaction.tables]) spec fullMember different
    change source.memory (record+8#64)=.word left at lc
    have leftEq : left=access:=HolWordLab.word.inj (lc.symm.trans state.field)
    have rightEq : right=table:=HolWordLab.word.inj (rc.symm.trans pointer)
    rw [leftEq,rightEq] at split
    dsimp only [FreshTransaction.firstTable] at split
    have currentImage : CurrentTable.New.ScalarEmpty post table spec.key spec.cap:=by
      apply image.of_memory domain
      intro entry entryMember
      apply frame.memory
      have lower:=CurrentTable.New.scalar_write_lower table spec.key spec.cap entry image.geometry.table entryMember
      have upper:=CurrentTable.New.scalar_write_before table spec.key spec.cap entry image.geometry.table entryMember
      rcases split with before|after
      · exact Or.inr (by omega)
      · exact Or.inl (by have endBefore:=image.geometry.header_before_end; omega)
    exact ⟨table,(recordMemory spec fullMember).trans pointer,currentImage,afterRecord,beforeHeap,endBeforeHeap⟩
  have current : FreshTransaction.Context origin post record bs heap FreshTransaction.remainingTables:=by
    refine ⟨runtime,by rw [globals]; exact context.recordCell,context.recordArena,context.recordAligned,
      by rw [globals]; exact context.heapCell,context.heapArena,context.heapBound,context.heapAligned,context.afterRecord,?_,context.valid,images,older,?_,?_⟩
    · exact (frame.memory record (Or.inl (by have lower:=state.afterRecord; omega))).trans context.blockField
    · intro name notHeap notRecord notCounter
      rw [globals]
      exact context.globals name notHeap notRecord notCounter
    · intro left lm right rm different
      exact separated left (List.mem_cons_of_mem FreshTransaction.firstTable lm) right (List.mem_cons_of_mem FreshTransaction.firstTable rm) different
  have field : post.memory (record+8#64)=.word access:=
    (recordMemory FreshTransaction.firstTable (by simp [FreshTransaction.tables])).trans state.field
  exact ⟨frame,current,field,separated,locals⟩

/-- The original pre-state helper's actual295-tick insertion prefix either
stops or reaches its unchanged block-cache getter with all other transaction
tables and earlier persistent memory retained from those same executions. -/
theorem to_after_set {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory} {record bs heap access pointer : BitVec 64}
    (context : FreshTransaction.Context origin source record bs heap FreshTransaction.remainingTables)
    (state : AccountAccess.AccessState source record access)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word pointer)))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    (source.clock-post.clock≤295 ∧ ∀ value,outcome≠some (.returned value)) ∨
      ∃ current inner,FreshTransaction.Context origin current record bs heap FreshTransaction.remainingTables ∧
        current.locals.lookup (ofString "addr")=some (.val (.word pointer)) ∧ current.clock≤source.clock ∧
        source.clock-current.clock≤295 ∧ CallPrefix.ScopeFrame post inner ∧ evaluateHOLFiniteState current afterSet=(outcome,inner) := by
  rw [body_shape] at run
  let actions : List CallPrefix.Action:=[.command AccountAccess.caller]
  change evaluateHOLFiniteState source (CallPrefix.program actions afterSet)=(outcome,post) at run
  have priced : source.clock-(evaluateHOLFiniteState source (CallPrefix.program actions .skip)).2.clock≤295:=by
    simpa only [actions,CallPrefix.program,Nat.add_zero] using ClockCost.sequence_current source AccountAccess.caller .skip 295 0
      (first_set_cost context state.field state.single addressCell) (ClockCost.skip source.code)
  rcases CallPrefix.priced_frame_trace source post actions afterSet 295 priced outcome run with stopped|reached
  · refine Or.inl ⟨stopped.1,?_⟩
    intro value returned
    have safe : LocalPrefix (ofString "addr") (CallPrefix.program actions .skip):=.seq (.call none _ _ (by simp)) .skip
    apply (safe.summary_full source).2.1 value
    rw [←stopped.2]
    exact returned
  · obtain ⟨entered,inner,execution,forward,price,scope,continued⟩:=reached
    have callerRun : evaluateHOLFiniteState source AccountAccess.caller=(none,entered):=by
      have actual:=execution.singleton
      cases actual with | command _ _ normal=>exact normal
    obtain ⟨frame,current,field,separated,locals⟩:=first_set_normal context state addressCell callerRun
    have currentAddress : entered.locals.lookup (ofString "addr")=some (.val (.word pointer)):=by rw [locals]; exact addressCell
    exact Or.inr ⟨entered,inner,current,currentAddress,forward,price,scope,continued⟩

end InitECandidate.Solver.Input.CurrentVerify.PreStateAccount

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountAccess.AccessState.of_erase
#print axioms InitECandidate.Solver.Input.CurrentVerify.PreStateAccount.call_entry_context
#print axioms InitECandidate.Solver.Input.CurrentVerify.PreStateAccount.first_set_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.PreStateAccount.to_after_set

namespace InitECandidate.Solver.Input.CurrentVerify.PreStateAccount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def cacheField : ExpHOL 64:=.op .add [.var .global (ofString "bs"),.const 16#64]
def getArguments : List (ExpHOL 64):=[.load .one cacheField,localVar "addr"]
def afterGet : ProgHOL 64:=match afterSet with | .decCall _ _ _ _ rest=>rest | _=>.skip
def missGuard : ProgHOL 64:=.ite (.cmp .notEqual (.rfield 0 (localVar "w")) (.const 0#64)) (.return (.rfield 1 (localVar "w"))) .skip
def afterMiss : ProgHOL 64:=match afterGet with | .seq _ rest=>rest | _=>.skip

theorem getter_shape : afterSet=.decCall (ofString "w") CurrentTable.Get.resultShape (ofString "htab_get") getArguments afterGet ∧
    afterGet=.seq missGuard afterMiss := by
  simp only [afterSet,afterGet,afterMiss,body,Guest.Software.guestFn_get_pre_state_account_optional,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,getArguments,cacheField,missGuard,localVar,CurrentTable.Get.resultShape,Option.map_none]
  trivial

theorem absent_after_get (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (cell : source.locals.lookup (ofString "w")=some CurrentTable.Get.absentValue) :
    evaluateHOLFiniteState source afterGet=evaluateHOLFiniteState source afterMiss := by
  have read : eval source (.cmp .notEqual (.rfield 0 (localVar "w")) (.const 0#64))=some (.val (.word 0#64)):=by
    simp [eval,evalHOLExact,toExact,localVar,cell,CurrentTable.Get.absentValue,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have skipped : evaluateHOLFiniteState source missGuard=(none,source):=by
    simp only [eval] at read
    rw [missGuard,evaluateHOLFiniteState_ite,read]
    simp [evaluateHOLFiniteState_skip]
  rw [getter_shape.2,evaluateHOLFiniteState_seq_line780,skipped]

/-- The real BS+16 cache metadata is obtained from the completed initializer
and its proved earlier-memory frame, independently of the requested address. -/
theorem cache_get_entry {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {cutoff ws bs pointer : BitVec 64}
    (records : RunAttempt.InitializedRecords origin source cutoff ws bs)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word pointer))) :
    ∃ table,CurrentTable.New.ScalarEmpty source table 20#64 256#64 ∧
      evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) getArguments=
        some [.val (.word table),.val (.word pointer)] := by
  have member : (⟨20,256,16⟩ : Mpt.StateInit.MemorySuffix.BlockTables.Spec)∈Mpt.StateInit.MemorySuffix.BlockTables.specs:=by decide
  obtain ⟨table,field,image,afterBs,beforeHeap⟩:=records.tables.1 _ member
  change source.memory (bs+16#64)=.word table at field
  have bsRead : eval source (.var .global (ofString "bs"))=some (.val (.word bs)):=by
    simp [eval,evalHOLExact,records.context.bsCell]
  have addressRead:=Scalar.plus_read source (.var .global (ofString "bs")) bs 16 bsRead
  have tableRead:=Witness.load_word_read source cacheField (bs+16#64) table addressRead
    (AllocatedBytes.word_mapped source bs 80 16 records.context.arena.domain records.context.bsArena (by decide) records.context.bsAligned (by decide)) field
  refine ⟨table,image,?_⟩
  simp only [eval] at tableRead
  simp only [getArguments,evalListHOLFinite,evalListHOLExact,tableRead]
  simp [evalHOLExact,localVar,addressCell]

/-- The actual first block-cache lookup either stops within two source
ticks or follows its proved absent result into the original miss suffix.
All transaction tables and initialized earlier block tables survive. -/
theorem cache_miss_trace {origin initialized source post : PanSemStateFiniteExact 64 Guest.HostMemory} {record cutoff ws bs heap pointer : BitVec 64}
    (context : FreshTransaction.Context origin source record bs heap FreshTransaction.remainingTables)
    (records : RunAttempt.InitializedRecords initialized source cutoff ws bs)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word pointer)))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterSet=(outcome,post)) :
    (source.clock-post.clock≤2 ∧ ∀ value,outcome≠some (.returned value)) ∨
      ∃ current inner,FreshTransaction.Context origin current record bs heap FreshTransaction.remainingTables ∧
        RunAttempt.InitializedRecords initialized current cutoff ws bs ∧
        current.locals.lookup (ofString "addr")=some (.val (.word pointer)) ∧ current.clock≤source.clock ∧
        source.clock-current.clock≤2 ∧ CallPrefix.ScopeFrame post inner ∧ evaluateHOLFiniteState current afterMiss=(outcome,inner) := by
  obtain ⟨table,image,args⟩:=cache_get_entry records addressCell
  rw [getter_shape.1] at run
  rcases CurrentTable.Get.scoped_scalar_empty_trace source post table 20#64 256#64 pointer image context.runtime.code "w" getArguments afterGet args outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨target,inner,frame,forward,price,continued,endpoint⟩:=reached
    let current:=CallNormal.continuationEntry source target "w" CurrentTable.Get.absentValue
    change evaluateHOLFiniteState current afterGet=(outcome,inner) at continued
    rw [absent_after_get current (CallNormal.continuation_lookup_same source target "w" CurrentTable.Get.absentValue)] at continued
    exact Or.inr ⟨current,inner,context.of_erase frame,records.of_erase frame,
      (CallNormal.continuation_lookup_other source target "w" "addr" CurrentTable.Get.absentValue (by decide)).trans addressCell,
      forward,price,(by rw [endpoint]; exact ⟨rfl,rfl⟩),continued⟩

/-- Complete actual prefix through both the repeated access insertion and
first BS-cache miss. The initialized snapshot is supplied at the real fresh
transaction origin and transported by the already proved physical frames. -/
theorem to_after_cache {origin initialized source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {record cutoff ws bs heap access pointer : BitVec 64}
    (context : FreshTransaction.Context origin source record bs heap FreshTransaction.remainingTables)
    (state : AccountAccess.AccessState source record access)
    (records : RunAttempt.InitializedRecords initialized origin cutoff ws bs) (before : cutoff.toNat≤record.toNat)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word pointer)))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    (source.clock-post.clock≤297 ∧ ∀ value,outcome≠some (.returned value)) ∨
      ∃ current inner,FreshTransaction.Context origin current record bs heap FreshTransaction.remainingTables ∧
        RunAttempt.InitializedRecords initialized current cutoff ws bs ∧
        current.locals.lookup (ofString "addr")=some (.val (.word pointer)) ∧ current.clock≤source.clock ∧
        source.clock-current.clock≤297 ∧ CallPrefix.ScopeFrame post inner ∧ evaluateHOLFiniteState current afterMiss=(outcome,inner) := by
  rcases to_after_set context state addressCell outcome run with stopped|reached
  · exact Or.inl ⟨by omega,stopped.2⟩
  · obtain ⟨entered,target,retained,currentAddress,forward,price,scope,continued⟩:=reached
    have currentRecords:=retained.initialized_records records before
    rcases cache_miss_trace retained currentRecords currentAddress outcome continued with stopped|reached
    · exact Or.inl ⟨by have clock:=scope.clock; omega,stopped.2⟩
    · obtain ⟨current,inner,last,lastRecords,lastAddress,nextForward,nextPrice,nextScope,rest⟩:=reached
      exact Or.inr ⟨current,inner,last,lastRecords,lastAddress,by omega,by omega,scope.trans nextScope,rest⟩

end InitECandidate.Solver.Input.CurrentVerify.PreStateAccount

#print axioms InitECandidate.Solver.Input.CurrentVerify.FreshTransaction.Context.initialized_records
#print axioms InitECandidate.Solver.Input.CurrentVerify.PreStateAccount.getter_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.PreStateAccount.absent_after_get
#print axioms InitECandidate.Solver.Input.CurrentVerify.PreStateAccount.cache_get_entry
#print axioms InitECandidate.Solver.Input.CurrentVerify.PreStateAccount.cache_miss_trace

#print axioms InitECandidate.Solver.Input.CurrentVerify.PreStateAccount.to_after_cache

namespace InitECandidate.Solver.Input.CurrentVerify.FreshTransaction
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- A real write to an earlier disjoint table retains the complete later
transaction state. Its earlier-memory snapshot is rebased to this new state. -/
theorem Context.after_earlier_scalar {origin source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {record bs heap table key cap : BitVec 64} {done : List TableSpec}
    (context : Context origin source record bs heap done)
    (frame : CurrentTable.New.ScalarFrame source target table key cap)
    (before : (CurrentTable.New.scalarNextHeap table key cap).toNat≤record.toNat) :
    Context target target record bs heap done := by
  have globals:=congrArg PanSemStateFiniteExact.globals frame.fields
  change target.globals=source.globals at globals
  have domain:=MemoryMetadata.domain frame.fields
  have code:=MemoryMetadata.code frame.fields
  have runtime : CurrentStartup.ArenaState target:=
    ⟨by rw [globals]; exact context.runtime.scratch,by rw [globals]; exact context.runtime.frame,
      domain.trans context.runtime.domain,by rw [code]; exact context.runtime.code⟩
  have fields (spec : TableSpec) (member : spec∈done) : target.memory (record+BitVec.ofNat 64 spec.offset)=source.memory (record+BitVec.ofNat 64 spec.offset):=by
    apply frame.memory
    apply Or.inr
    rw [record_address_number record context.recordArena spec.offset (context.valid spec member).2.1]
    omega
  refine ⟨runtime,by rw [globals]; exact context.recordCell,context.recordArena,context.recordAligned,
    by rw [globals]; exact context.heapCell,context.heapArena,context.heapBound,context.heapAligned,context.afterRecord,
    (frame.memory record (Or.inr before)).trans context.blockField,context.valid,?_,?_,by intros; rfl,context.separated.of_memory fields⟩
  · intro spec member
    obtain ⟨other,field,image,afterRecord,beforeHeap,endBeforeHeap⟩:=context.images spec member
    refine ⟨other,(fields spec member).trans field,?_,afterRecord,beforeHeap,endBeforeHeap⟩
    apply image.of_memory domain
    intro entry present
    apply frame.memory
    apply Or.inr
    have lower:=CurrentTable.New.scalar_write_lower other _ _ entry image.geometry.table present
    omega
  · exact ⟨⟨heap,by rw [globals]; exact context.heapCell,context.heapArena,context.heapBound,context.heapAligned,
        by have lower:=context.afterRecord; omega⟩,rfl,by intros; rfl⟩

end InitECandidate.Solver.Input.CurrentVerify.FreshTransaction

namespace InitECandidate.Solver.Input.CurrentVerify.RecordPreStateRead
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def body : ProgHOL 64:=match Guest.Software.guestFn_record_pre_state_read with | .function fn=>progToHOL fn.body | _=>.skip
def field : ExpHOL 64:=.op .add [.var .global (ofString "bs"),.const 72#64]
def arguments : List (ExpHOL 64):=[.load .one field,localVar "addr",.const 1#64]
def setCall : ProgHOL 64:=.call (some (none,none)) (ofString "htab_set") arguments

theorem body_shape : body=.seq setCall (.return (.const 0#64)) := by
  simp only [body,Guest.Software.guestFn_record_pre_state_read,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    setCall,arguments,field,localVar,Option.map_none]

theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "record_pre_state_read")=some ([(ofString "addr",.one)],body,.one) := by
  have found:=OriginalCode.indexed code installed 330
    (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_record_pre_state_read) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,
    Guest.Software.guestFn_record_pre_state_read,paramToHOL,shapeToHOL,List.map_cons,List.map_nil] using found

/-- The actual read-recording table and setter arguments follow from its
BS+72 cell and the completed initializer, with no future read-success premise. -/
theorem set_entry {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {cutoff ws bs pointer : BitVec 64}
    (records : RunAttempt.InitializedRecords origin source cutoff ws bs)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word pointer))) :
    ∃ table,source.memory (bs+72#64)=.word table ∧ CurrentTable.New.ScalarEmpty source table 20#64 256#64 ∧
      bs.toNat+80≤table.toNat ∧ (CurrentTable.New.scalarNextHeap table 20#64 256#64).toNat≤cutoff.toNat ∧
      evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
        some [.val (.word table),.val (.word pointer),.val (.word 1#64)] := by
  have member : (⟨20,256,72⟩ : Mpt.StateInit.MemorySuffix.BlockTables.Spec)∈Mpt.StateInit.MemorySuffix.BlockTables.specs:=by decide
  obtain ⟨table,cell,image,afterBs,beforeHeap⟩:=records.tables.1 _ member
  change source.memory (bs+72#64)=.word table at cell
  have bsRead : eval source (.var .global (ofString "bs"))=some (.val (.word bs)):=by
    simp [eval,evalHOLExact,records.context.bsCell]
  have addressRead:=Scalar.plus_read source (.var .global (ofString "bs")) bs 72 bsRead
  have tableRead:=Witness.load_word_read source field (bs+72#64) table addressRead
    (AllocatedBytes.word_mapped source bs 80 72 records.context.arena.domain records.context.bsArena (by decide) records.context.bsAligned (by decide)) cell
  refine ⟨table,cell,image,afterBs,beforeHeap,?_⟩
  simp only [eval] at tableRead
  simp only [arguments,evalListHOLFinite,evalListHOLExact,tableRead]
  simp [evalHOLExact,localVar,addressCell]

/-- Complete unchanged body, including every failed read/copy/store or
clock-zero outcome of its actual first insertion. -/
theorem body_cost {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {cutoff ws bs pointer : BitVec 64}
    (records : RunAttempt.InitializedRecords origin source cutoff ws bs)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word pointer))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤29 := by
  obtain ⟨table,field,image,afterBs,beforeHeap,args⟩:=set_entry records addressCell
  have cost:=CurrentTable.Set.account_first_call_cost source table 256#64 pointer 1#64 image records.context.arena.code arguments args
  rw [body_shape]
  exact ClockCost.sequence_current source setCall (.return (.const 0#64)) 29 0 cost (ClockCost.returned source.code _)

end InitECandidate.Solver.Input.CurrentVerify.RecordPreStateRead

#print axioms InitECandidate.Solver.Input.CurrentVerify.FreshTransaction.Context.after_earlier_scalar
#print axioms InitECandidate.Solver.Input.CurrentVerify.RecordPreStateRead.body_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.RecordPreStateRead.original_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.RecordPreStateRead.set_entry
#print axioms InitECandidate.Solver.Input.CurrentVerify.RecordPreStateRead.body_cost

namespace InitECandidate.Solver.Input.CurrentVerify.RecordPreStateRead
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def remainingSpecs : List Mpt.StateInit.MemorySuffix.BlockTables.Spec:=
  Mpt.StateInit.MemorySuffix.BlockTables.specs.filter (fun spec=>decide (spec.offset≠72))

/-- The first actual recording has changed BS+72 into a singleton. Other
block tables and the later transaction tables retain their images; earlier
WS/MPT contents are protected only below BS+80, where no write occurred. -/
structure Recorded (origin current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (cutoff ws bs table record heap : BitVec 64) : Prop where
  records : RunAttempt.RetainedRecords origin current (bs+80#64) ws bs
  tableCell : current.memory (bs+72#64)=.word table
  single : CurrentTable.New.ScalarSingle current table 20#64 256#64 1#64 1#64
  afterBs : bs.toNat+80≤table.toNat
  beforeCutoff : (CurrentTable.New.scalarNextHeap table 20#64 256#64).toNat≤cutoff.toNat
  images : Mpt.StateInit.MemorySuffix.BlockTables.Images current bs cutoff remainingSpecs
  separated : Mpt.StateInit.MemorySuffix.BlockTables.Separated current bs Mpt.StateInit.MemorySuffix.BlockTables.specs
  fresh : ∃ freshOrigin,FreshTransaction.Context freshOrigin current record bs heap FreshTransaction.remainingTables
  initialized : Mpt.StateInit.WorldState origin ws bs
  lower : 2701135464≤ws.toNat

/-- A proved scalar write footprint transports exactly the unaffected
initialization facts. It does not preserve the modified table as empty. -/
theorem recorded_of_frame {origin freshOrigin source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {cutoff ws bs table record heap : BitVec 64}
    (records : RunAttempt.InitializedRecords origin source cutoff ws bs)
    (context : FreshTransaction.Context freshOrigin source record bs heap FreshTransaction.remainingTables)
    (before : cutoff.toNat≤record.toNat)
    (tableCell : source.memory (bs+72#64)=.word table)
    (afterBs : bs.toNat+80≤table.toNat)
    (beforeCutoff : (CurrentTable.New.scalarNextHeap table 20#64 256#64).toNat≤cutoff.toNat)
    (frame : CurrentTable.New.ScalarFrame source post table 20#64 256#64)
    (single : CurrentTable.New.ScalarSingle post table 20#64 256#64 1#64 1#64) :
    Recorded origin post cutoff ws bs table record heap := by
  have globals:=congrArg PanSemStateFiniteExact.globals frame.fields
  change post.globals=source.globals at globals
  have domain:=MemoryMetadata.domain frame.fields
  have fresh:=context.after_earlier_scalar frame (Nat.le_trans beforeCutoff before)
  have number : (bs+80#64).toNat=bs.toNat+80:=byteAddress_toNat bs 80 (by have upper:=records.context.bsArena.upper; omega)
  have reduced : RunAttempt.RetainedRecords origin source (bs+80#64) ws bs:=by
    refine ⟨records.context,by rw [number],?_⟩
    intro query low high
    apply records.memory query low
    rw [number] at high
    have earlier:=records.before
    omega
  have retained : RunAttempt.RetainedRecords origin post (bs+80#64) ws bs:=by
    apply reduced.after fresh.runtime
      ⟨heap,fresh.heapCell,by rw [number]; have extent:=context.afterRecord; have oldBefore:=records.before; omega,
        fresh.heapBound,fresh.heapAligned⟩
      (by rw [globals]) (by rw [globals])
    intro query low high
    apply frame.memory
    apply Or.inl
    rw [number] at high
    omega
  have valid : ∀ spec∈Mpt.StateInit.MemorySuffix.BlockTables.specs,spec.Valid:=by
    obtain ⟨cursor,initialized⟩:=records.initialized.tables
    exact initialized.valid
  have fields (spec : Mpt.StateInit.MemorySuffix.BlockTables.Spec) (member : spec∈Mpt.StateInit.MemorySuffix.BlockTables.specs) :
      post.memory (bs+BitVec.ofNat 64 spec.offset)=source.memory (bs+BitVec.ofNat 64 spec.offset):=by
    have inside:=(valid spec member).2.1
    have address:=byteAddress_toNat bs spec.offset (by have upper:=records.context.bsArena.upper; omega)
    change (bs+BitVec.ofNat 64 spec.offset).toNat=bs.toNat+spec.offset at address
    apply frame.memory
    apply Or.inl
    rw [address]
    omega
  have readMember : (⟨20,256,72⟩ : Mpt.StateInit.MemorySuffix.BlockTables.Spec)∈Mpt.StateInit.MemorySuffix.BlockTables.specs:=by decide
  refine ⟨retained,(fields _ readMember).trans tableCell,single,afterBs,beforeCutoff,?_,records.tables.2.of_memory fields,⟨post,fresh⟩,records.initialized,records.lower⟩
  intro spec member
  have fullMember : spec∈Mpt.StateInit.MemorySuffix.BlockTables.specs:=(List.mem_filter.mp member).1
  have different : spec.offset≠72:=of_decide_eq_true (List.mem_filter.mp member).2
  obtain ⟨other,pointer,image,otherAfter,otherBefore⟩:=records.tables.1 spec fullMember
  obtain ⟨left,right,lc,rc,split⟩:=records.tables.2 _ readMember spec fullMember (Ne.symm different)
  change source.memory (bs+72#64)=.word left at lc
  have leftEq : left=table:=HolWordLab.word.inj (lc.symm.trans tableCell)
  have rightEq : right=other:=HolWordLab.word.inj (rc.symm.trans pointer)
  rw [leftEq,rightEq] at split
  refine ⟨other,(fields spec fullMember).trans pointer,?_,otherAfter,otherBefore⟩
  apply image.of_memory domain
  intro entry present
  have low:=CurrentTable.New.scalar_write_lower other _ _ entry image.geometry.table present
  have high:=CurrentTable.New.scalar_write_before other _ _ entry image.geometry.table present
  apply frame.memory
  rcases split with first|second
  · exact Or.inr (by change (CurrentTable.New.scalarNextHeap table 20#64 256#64).toNat≤other.toNat at first; omega)
  · exact Or.inl (by have endBefore:=image.geometry.header_before_end; omega)

/-- Every actual normal body return supplies its zero result, singleton
and complete external memory frame, including the literal final return. -/
theorem body_normal {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory} {cutoff ws bs pointer : BitVec 64}
    (records : RunAttempt.InitializedRecords origin source cutoff ws bs)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word pointer)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ ∃ table,source.memory (bs+72#64)=.word table ∧
      bs.toNat+80≤table.toNat ∧ (CurrentTable.New.scalarNextHeap table 20#64 256#64).toNat≤cutoff.toNat ∧
      CurrentTable.New.ScalarFrame source post table 20#64 256#64 ∧
      CurrentTable.New.ScalarSingle post table 20#64 256#64 1#64 1#64 := by
  obtain ⟨table,cell,image,afterBs,beforeHeap,args⟩:=set_entry records addressCell
  rw [body_shape] at normal
  have safe : LocalPrefix (ofString "_") setCall:=.call none _ _ (by simp)
  obtain ⟨middle,setRun,returned,preserved⟩:=safe.normal_continue source post (.return (.const 0#64)) value normal
  obtain ⟨frame,locals,single⟩:=CurrentTable.Set.scalar_empty_call_frame image records.context.arena.code arguments args (by decide) (by decide) setRun
  obtain ⟨read,endpoint⟩:=return_normal middle post (.const 0#64) value returned
  have answer : value=.val (.word 0#64):=by simpa [eval,evalHOLExact] using read.symm
  have same : LocalEffects.erase post=LocalEffects.erase middle:=by rw [endpoint]; rfl
  exact ⟨answer,table,cell,afterBs,beforeHeap,frame.of_erase rfl same,single.of_erase same⟩

end InitECandidate.Solver.Input.CurrentVerify.RecordPreStateRead

#print axioms InitECandidate.Solver.Input.CurrentVerify.RecordPreStateRead.recorded_of_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.RecordPreStateRead.body_normal

namespace InitECandidate.Solver.Input.CurrentVerify.RecordPreStateRead
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem call_cost {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {cutoff ws bs : BitVec 64}
    (records : RunAttempt.InitializedRecords origin source cutoff ws bs) (pointer : BitVec 64) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word pointer)]) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "record_pre_state_read") expressions)).2.clock≤30 := by
  obtain ⟨callee,called,addressCell⟩:=CallNormal.unary_environment source.code.lookup (ofString "record_pre_state_read") "addr" body pointer
    (original_code source.code records.context.arena.code)
  have cost:=body_cost (records.of_erase (show LocalEffects.erase (callEntryStateHOLFinite source callee)=LocalEffects.erase source from rfl)) addressCell
  exact ClockCost.call_current source (some none) (ofString "record_pre_state_read") expressions _ body callee .one 29 args called cost

/-- The real ordinary recording call establishes its modified block table,
retained other tables and older workspace contents at restored caller locals. -/
theorem call_normal {origin freshOrigin source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {cutoff ws bs record heap pointer : BitVec 64}
    (records : RunAttempt.InitializedRecords origin source cutoff ws bs)
    (context : FreshTransaction.Context freshOrigin source record bs heap FreshTransaction.remainingTables)
    (before : cutoff.toNat≤record.toNat) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word pointer)])
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "record_pre_state_read") expressions)=(none,post)) :
    ∃ table,Recorded origin post cutoff ws bs table record heap ∧
      CurrentTable.New.ScalarFrame source post table 20#64 256#64 ∧ post.locals=source.locals := by
  obtain ⟨callee,called,addressCell⟩:=CallNormal.unary_environment source.code.lookup (ofString "record_pre_state_read") "addr" body pointer
    (original_code source.code records.context.arena.code)
  obtain ⟨funded,values,actual,actualCallee,shape,target,value,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩:=
    CallNormal.ignored_data source post (ofString "record_pre_state_read") expressions normal
  have valuesEq : values=[.val (.word pointer)]:=Option.some.inj (actualArgs.symm.trans args)
  subst values
  have entryEq : (actual,actualCallee,shape)=(body,callee,.one):=Option.some.inj (actualCalled.symm.trans called)
  cases entryEq
  obtain ⟨answer,table,cell,afterBs,beforeHeap,frame,single⟩:=body_normal
    (records.of_erase (show LocalEffects.erase (callEntryStateHOLFinite source callee)=LocalEffects.erase source from rfl)) addressCell value bodyRun
  have currentFrame : CurrentTable.New.ScalarFrame source post table 20#64 256#64:=frame.of_erase rfl (by rw [endpoint]; rfl)
  have currentSingle : CurrentTable.New.ScalarSingle post table 20#64 256#64 1#64 1#64:=single.of_erase (by rw [endpoint]; rfl)
  exact ⟨table,recorded_of_frame records context before cell afterBs beforeHeap currentFrame currentSingle,currentFrame,by rw [endpoint]⟩

end InitECandidate.Solver.Input.CurrentVerify.RecordPreStateRead

namespace InitECandidate.Solver.Input.CurrentVerify.PreStateAccount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def recordCall : ProgHOL 64:=.call (some (none,none)) (ofString "record_pre_state_read") [localVar "addr"]
def afterRecord : ProgHOL 64:=match afterMiss with | .seq _ rest=>rest | _=>.skip

theorem record_shape : afterMiss=.seq recordCall afterRecord := by
  simp only [afterRecord,afterMiss,afterGet,afterSet,body,Guest.Software.guestFn_get_pre_state_account_optional,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,recordCall,localVar,Option.map_none]

/-- Recording the first actual pre-state read costs at most30 caller ticks
and reaches the unchanged workspace-account caller with its own new state. -/
theorem miss_record_trace_complete {origin initialized source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {record cutoff ws bs heap pointer : BitVec 64}
    (context : FreshTransaction.Context origin source record bs heap FreshTransaction.remainingTables)
    (records : RunAttempt.InitializedRecords initialized source cutoff ws bs) (before : cutoff.toNat≤record.toNat)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word pointer)))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterMiss=(outcome,post)) :
    (source.clock-post.clock≤30 ∧ ∀ value,outcome≠some (.returned value)) ∨
      ∃ current inner table,RecordPreStateRead.Recorded initialized current cutoff ws bs table record heap ∧
        current.locals.lookup (ofString "addr")=some (.val (.word pointer)) ∧ current.clock≤source.clock ∧
        source.clock-current.clock≤30 ∧ CallPrefix.ScopeFrame post inner ∧ evaluateHOLFiniteState current afterRecord=(outcome,inner) ∧
        MemoryMetadata.erase current=MemoryMetadata.erase source := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "addr"]=some [.val (.word pointer)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,addressCell]
  rw [record_shape] at run
  let actions : List CallPrefix.Action:=[.command recordCall]
  change evaluateHOLFiniteState source (CallPrefix.program actions afterRecord)=(outcome,post) at run
  have priced : source.clock-(evaluateHOLFiniteState source (CallPrefix.program actions .skip)).2.clock≤30:=by
    simpa only [actions,CallPrefix.program,Nat.add_zero] using ClockCost.sequence_current source recordCall .skip 30 0
      (RecordPreStateRead.call_cost records pointer [localVar "addr"] args) (ClockCost.skip source.code)
  rcases CallPrefix.priced_frame_trace source post actions afterRecord 30 priced outcome run with stopped|reached
  · refine Or.inl ⟨stopped.1,?_⟩
    intro value returned
    have safe : LocalPrefix (ofString "addr") (CallPrefix.program actions .skip):=.seq (.call none _ _ (by simp)) .skip
    apply (safe.summary_full source).2.1 value
    rw [←stopped.2]
    exact returned
  · obtain ⟨current,inner,execution,forward,price,scope,continued⟩:=reached
    have actual : evaluateHOLFiniteState source recordCall=(none,current):=by
      have first:=execution.singleton
      cases first with | command _ _ normal=>exact normal
    obtain ⟨table,state,frame,locals⟩:=RecordPreStateRead.call_normal records context before [localVar "addr"] args actual
    exact Or.inr ⟨current,inner,table,state,(by rw [locals]; exact addressCell),forward,price,scope,continued,frame.fields⟩

theorem miss_record_trace {origin initialized source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {record cutoff ws bs heap pointer : BitVec 64}
    (context : FreshTransaction.Context origin source record bs heap FreshTransaction.remainingTables)
    (records : RunAttempt.InitializedRecords initialized source cutoff ws bs) (before : cutoff.toNat≤record.toNat)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word pointer)))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterMiss=(outcome,post)) :
    (source.clock-post.clock≤30 ∧ ∀ value,outcome≠some (.returned value)) ∨
      ∃ current inner table,RecordPreStateRead.Recorded initialized current cutoff ws bs table record heap ∧
        current.locals.lookup (ofString "addr")=some (.val (.word pointer)) ∧ current.clock≤source.clock ∧
        source.clock-current.clock≤30 ∧ CallPrefix.ScopeFrame post inner ∧ evaluateHOLFiniteState current afterRecord=(outcome,inner) := by
  rcases miss_record_trace_complete context records before addressCell outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨current,inner,table,state,address,forward,price,scope,continued,metadata⟩:=reached
    exact Or.inr ⟨current,inner,table,state,address,forward,price,scope,continued⟩

/-- Whole unchanged pre-state prefix through the repeated access insertion,
BS-cache miss and real pre-state-read recording, on every actual outcome. -/
theorem to_after_record {origin initialized source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {record cutoff ws bs heap access pointer : BitVec 64}
    (context : FreshTransaction.Context origin source record bs heap FreshTransaction.remainingTables)
    (state : AccountAccess.AccessState source record access)
    (records : RunAttempt.InitializedRecords initialized origin cutoff ws bs) (before : cutoff.toNat≤record.toNat)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word pointer)))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    (source.clock-post.clock≤327 ∧ ∀ value,outcome≠some (.returned value)) ∨
      ∃ current inner table,RecordPreStateRead.Recorded initialized current cutoff ws bs table record heap ∧
        current.locals.lookup (ofString "addr")=some (.val (.word pointer)) ∧ current.clock≤source.clock ∧
        source.clock-current.clock≤327 ∧ CallPrefix.ScopeFrame post inner ∧ evaluateHOLFiniteState current afterRecord=(outcome,inner) := by
  rcases to_after_cache context state records before addressCell outcome run with stopped|reached
  · exact Or.inl ⟨by omega,stopped.2⟩
  · obtain ⟨entered,target,retained,currentRecords,currentAddress,forward,price,scope,continued⟩:=reached
    rcases miss_record_trace retained currentRecords before currentAddress outcome continued with stopped|reached
    · exact Or.inl ⟨by have clock:=scope.clock; omega,stopped.2⟩
    · obtain ⟨current,inner,table,last,lastAddress,nextForward,nextPrice,nextScope,rest⟩:=reached
      exact Or.inr ⟨current,inner,table,last,lastAddress,by omega,by omega,scope.trans nextScope,rest⟩

end InitECandidate.Solver.Input.CurrentVerify.PreStateAccount

#print axioms InitECandidate.Solver.Input.CurrentVerify.RecordPreStateRead.call_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.RecordPreStateRead.call_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.PreStateAccount.record_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.PreStateAccount.miss_record_trace
#print axioms InitECandidate.Solver.Input.CurrentVerify.PreStateAccount.to_after_record

namespace InitECandidate.Solver.Input.CurrentVerify.RecordPreStateRead
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The actual first read-recording mutation preserves the initialized
workspace root, its closed trie and bounded values. Every needed field is
below BS, inside the narrower earlier-memory frame proved for that write. -/
theorem Recorded.world {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {cutoff ws bs table record heap : BitVec 64} (state : Recorded origin source cutoff ws bs table record heap) :
    ∃ db node,db.toNat≤ws.toNat ∧ source.memory (ws+24#64)=.word node ∧
      ∃ registry : Mpt.WitnessCore.NodeRegistry source (ws.toNat+40) bs db,registry.graph.valid node := by
  obtain ⟨db,node,dbBefore,cell,registry,member⟩:=state.initialized.world
  have domain : source.memaddrs=origin.memaddrs:=state.records.context.arena.domain.trans state.initialized.memory.arena.domain.symm
  have cutoffNumber : (bs+80#64).toNat=bs.toNat+80:=byteAddress_toNat bs 80 (by have upper:=state.records.context.bsArena.upper; omega)
  have ws24 : (ws+24#64).toNat=ws.toNat+24:=byteAddress_toNat ws 24 (by have upper:=state.records.context.wsArena.upper; omega)
  have rootMemory : source.memory (ws+24#64)=origin.memory (ws+24#64):=by
    apply state.records.memory
    · rw [ws24]; have lower:=state.lower; omega
    · rw [ws24,cutoffNumber]; have before:=state.records.context.wsBeforeBs; omega
  have agree : ∀ query,registry.graph.Footprint query→source.memory query=origin.memory query:=by
    intro query required
    have bounds:=registry.graph.footprint_bounds (ws.toNat+40) bs.toNat registry.regions query required
    apply state.records.memory
    · have lower:=state.lower; omega
    · rw [cutoffNumber]; omega
  have valueAgree : ∀ query,Mpt.TrieWalk.ValueFootprint registry.graph query→source.memory query=origin.memory query:=by
    intro query required
    have bounds:=registry.graph.value_bounds (ws.toNat+40) bs.toNat registry.regions query required
    apply state.records.memory
    · have lower:=state.lower; omega
    · rw [cutoffNumber]; omega
  obtain ⟨graph,validEq,regions,disjoint,⟨values⟩⟩:=registry.graph.after_agreement origin source 1024 (ws.toNat+40) bs.toNat (Mpt.WitnessCore.WitnessValue db)
    registry.values registry.regions registry.disjoint domain agree valueAgree
  refine ⟨db,node,dbBefore,rootMemory.trans cell,⟨graph,values,regions,disjoint⟩,?_⟩
  change graph.valid node
  rw [validEq]
  exact member

end InitECandidate.Solver.Input.CurrentVerify.RecordPreStateRead

#print axioms InitECandidate.Solver.Input.CurrentVerify.RecordPreStateRead.Recorded.world

namespace InitECandidate.Solver.Input.CurrentVerify.RecordPreStateRead
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The actual initialized trie retained by read recording lies beyond the
fixed nibble buffer. Key conversion therefore protects all structural and
value fields, rather than assuming a protected future lookup graph. -/
theorem Recorded.lookup_world {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {cutoff ws bs table record heap : BitVec 64} (state : Recorded origin source cutoff ws bs table record heap) :
    ∃ db node,db.toNat≤ws.toNat ∧ source.memory (ws+24#64)=.word node ∧
      ∃ registry : Mpt.WitnessCore.NodeRegistry source (ws.toNat+40) bs db,
        registry.graph.valid node ∧ registry.graph.Protected 2701134704#64 ∧
        Mpt.TrieWalk.ValueProtected registry.graph 2701134704#64 := by
  obtain ⟨db,node,dbBefore,stored,registry,member⟩:=state.world
  refine ⟨db,node,dbBefore,stored,registry,member,?_,?_⟩
  · intro query required offset inside
    have lower:=(registry.graph.footprint_bounds (ws.toNat+40) bs.toNat registry.regions query required).1
    exact (CopyGeneral.Away.before 2701134704#64 query 64 2701134768 (by decide) (by decide)
      (by have wsLower:=state.lower; omega) offset inside).2
  · intro query required offset inside
    have lower:=(registry.graph.value_bounds (ws.toNat+40) bs.toNat registry.regions query required).1
    exact (CopyGeneral.Away.before 2701134704#64 query 64 2701134768 (by decide) (by decide)
      (by have wsLower:=state.lower; omega) offset inside).2

/-- The retained workspace record itself supplies the real mapped root
word and typed WS global at this reached account lookup. -/
theorem Recorded.root_cell {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {cutoff ws bs table record heap : BitVec 64} (state : Recorded origin source cutoff ws bs table record heap) :
    source.globals.lookup (ofString "ws")=some (.val (.word ws)) ∧ source.memaddrs (ws+24#64) := by
  refine ⟨state.records.context.wsCell,?_⟩
  simpa only [byteAddress] using AllocatedBytes.word_mapped source ws 40 24 state.records.context.arena.domain
    state.records.context.wsArena (by decide) state.records.context.wsAligned (by decide)

end InitECandidate.Solver.Input.CurrentVerify.RecordPreStateRead

#print axioms InitECandidate.Solver.Input.CurrentVerify.RecordPreStateRead.Recorded.lookup_world
#print axioms InitECandidate.Solver.Input.CurrentVerify.RecordPreStateRead.Recorded.root_cell

namespace InitECandidate.Solver.Input.CurrentVerify.AccountLookup
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Startup workspace facts needed at the first actual account lookup.
These facts impose no address readability or later hash success. -/
structure Environment (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  keccak : CurrentKeccak.Hash.Environment source 2701132160#64 2701132360#64
  little : source.be=false
  nibbles : source.globals.lookup (ofString "mpt_nib_scratch")=some (.val (.word 2701134704#64))
  arena : CurrentStartup.ArenaState source

theorem Environment.of_metadata {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (ready : Environment source) (frame : MemoryMetadata.erase target=MemoryMetadata.erase source) : Environment target := by
  have code:=MemoryMetadata.code frame
  have domain:=MemoryMetadata.domain frame
  have endian:=MemoryMetadata.endian frame
  have globals:=congrArg PanSemStateFiniteExact.globals frame
  change target.globals=source.globals at globals
  exact ⟨⟨by rw [code]; exact ready.keccak.installed,domain.trans ready.keccak.domain,
    by rw [globals]; exact ready.keccak.stateGlobal,by rw [globals]; exact ready.keccak.padGlobal,
    ready.keccak.stateArena,ready.keccak.padArena,ready.keccak.stateAligned,ready.keccak.padAligned⟩,
    endian.trans ready.little,(by rw [globals]; exact ready.nibbles),
    ⟨by rw [globals]; exact ready.arena.scratch,by rw [globals]; exact ready.arena.frame,
      domain.trans ready.arena.domain,by rw [code]; exact ready.arena.code⟩⟩

end InitECandidate.Solver.Input.CurrentVerify.AccountLookup

namespace InitECandidate.Solver.Input.CurrentVerify
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The real main input producer already derives every lookup workspace
cell; extracting them does not assume any later account execution. -/
theorem Data.account_lookup_environment {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary) :
    AccountLookup.Environment source := ⟨data.keccak,data.little,data.mptNibs,data.arena⟩

/-- The genuine fresh-state frame allows its heap, TS and journal counter
to change while retaining the actual startup hash/nibble cells and endian. -/
theorem FreshTransaction.Context.account_lookup_environment {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {record bs heap : BitVec 64} {done : List FreshTransaction.TableSpec}
    (context : FreshTransaction.Context origin source record bs heap done) (ready : AccountLookup.Environment origin) :
    AccountLookup.Environment source := by
  have endian:=MemoryMetadata.endian context.older.metadata
  change source.be=origin.be at endian
  exact ⟨⟨context.runtime.code,context.runtime.domain,
    (context.globals _ (by decide) (by decide) (by decide)).trans ready.keccak.stateGlobal,
    (context.globals _ (by decide) (by decide) (by decide)).trans ready.keccak.padGlobal,
    ready.keccak.stateArena,ready.keccak.padArena,ready.keccak.stateAligned,ready.keccak.padAligned⟩,
    endian.trans ready.little,(context.globals _ (by decide) (by decide) (by decide)).trans ready.nibbles,context.runtime⟩

end InitECandidate.Solver.Input.CurrentVerify

namespace InitECandidate.Solver.Input.CurrentVerify.PreStateAccount
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The same actual327tick prefix now supplies the original workspace
cells at ws_get_account_optional, together with its recorded initialized
trie. No workspace fact at the future continuation is a premise. -/
theorem to_after_record_environment {origin initialized source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {record cutoff ws bs heap access pointer : BitVec 64}
    (context : FreshTransaction.Context origin source record bs heap FreshTransaction.remainingTables)
    (state : AccountAccess.AccessState source record access)
    (records : RunAttempt.InitializedRecords initialized origin cutoff ws bs) (before : cutoff.toNat≤record.toNat)
    (ready : AccountLookup.Environment origin)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word pointer)))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    (source.clock-post.clock≤327 ∧ ∀ value,outcome≠some (.returned value)) ∨
      ∃ current inner table,RecordPreStateRead.Recorded initialized current cutoff ws bs table record heap ∧
        AccountLookup.Environment current ∧ current.locals.lookup (ofString "addr")=some (.val (.word pointer)) ∧ current.clock≤source.clock ∧
        source.clock-current.clock≤327 ∧ CallPrefix.ScopeFrame post inner ∧ evaluateHOLFiniteState current afterRecord=(outcome,inner) := by
  rcases to_after_cache context state records before addressCell outcome run with stopped|reached
  · exact Or.inl ⟨by omega,stopped.2⟩
  · obtain ⟨entered,target,retained,currentRecords,currentAddress,forward,price,scope,continued⟩:=reached
    have currentReady:=retained.account_lookup_environment ready
    rcases miss_record_trace_complete retained currentRecords before currentAddress outcome continued with stopped|reached
    · exact Or.inl ⟨by have clock:=scope.clock; omega,stopped.2⟩
    · obtain ⟨current,inner,table,last,lastAddress,nextForward,nextPrice,nextScope,rest,metadata⟩:=reached
      exact Or.inr ⟨current,inner,table,last,currentReady.of_metadata metadata,lastAddress,by omega,by omega,scope.trans nextScope,rest⟩

end InitECandidate.Solver.Input.CurrentVerify.PreStateAccount

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Environment.of_metadata
#print axioms InitECandidate.Solver.Input.CurrentVerify.Data.account_lookup_environment
#print axioms InitECandidate.Solver.Input.CurrentVerify.FreshTransaction.Context.account_lookup_environment
#print axioms InitECandidate.Solver.Input.CurrentVerify.PreStateAccount.miss_record_trace_complete
#print axioms InitECandidate.Solver.Input.CurrentVerify.PreStateAccount.to_after_record_environment

namespace InitECandidate.Solver.Input.CurrentVerify.AccountLookup
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Physical entry supplied by the genuine first pre-state prefix. The
actual heap follows BS, while the initialized trie lies between WS and BS.
No temporary allocation room, hash output or later account result is supplied. -/
structure Entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ws bs : BitVec 64) : Prop where
  environment : Environment source
  wsCell : source.globals.lookup (ofString "ws")=some (.val (.word ws))
  wsArena : AllocatedBytes.Arena ws 40
  wsAligned : ws.toNat%8=0
  lower : 2701135464≤ws.toNat
  wsBeforeBs : ws.toNat+40≤bs.toNat
  heap : NormalHeapEffects.AtLeast (bs.toNat+80) source
  world : ∃ db node,db.toNat≤ws.toNat ∧ source.memory (ws+24#64)=.word node ∧
    ∃ registry : Mpt.WitnessCore.NodeRegistry source (ws.toNat+40) bs db,registry.graph.valid node

/-- Both inputs are conclusions of the same original pre-state prefix:
its recorded initialized state and its retained startup workspace cells. -/
theorem Entry.of_recorded {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {cutoff ws bs table record heap : BitVec 64}
    (state : RecordPreStateRead.Recorded origin source cutoff ws bs table record heap) (ready : Environment source) :
    Entry source ws bs :=
  ⟨ready,state.records.context.wsCell,state.records.context.wsArena,state.records.context.wsAligned,state.lower,
    state.records.context.wsBeforeBs,state.records.context.afterBs,state.world⟩

/-- Entering a real helper or changing lexical bindings preserves this
physical entry. The current registry is transported, rather than postulated. -/
theorem Entry.of_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {ws bs : BitVec 64}
    (entry : Entry source ws bs) (frame : LocalEffects.erase target=LocalEffects.erase source) : Entry target ws bs := by
  have memory:=LocalEffects.memory_of_erase source target frame
  have domain:=congrArg PanSemStateFiniteExact.memaddrs frame
  have globals:=congrArg PanSemStateFiniteExact.globals frame
  change target.memaddrs=source.memaddrs at domain
  change target.globals=source.globals at globals
  obtain ⟨heap,cell,lower,bounded,aligned⟩:=entry.heap
  refine ⟨entry.environment.of_metadata (MemoryMetadata.of_frame frame),by rw [globals]; exact entry.wsCell,
    entry.wsArena,entry.wsAligned,entry.lower,entry.wsBeforeBs,
    ⟨heap,by rw [globals]; exact cell,lower,bounded,aligned⟩,?_⟩
  obtain ⟨db,node,dbBefore,stored,registry,member⟩:=entry.world
  obtain ⟨graph,validEq,regions,disjoint,⟨values⟩⟩:=registry.graph.after_agreement source target 1024 (ws.toNat+40) bs.toNat (Mpt.WitnessCore.WitnessValue db)
    registry.values registry.regions registry.disjoint domain (fun _ _=>congrFun memory _) (fun _ _=>congrFun memory _)
  refine ⟨db,node,dbBefore,(congrFun memory _).trans stored,⟨graph,values,regions,disjoint⟩,?_⟩
  change graph.valid node
  rw [validEq]
  exact member

theorem Entry.root_mapped {source : PanSemStateFiniteExact 64 Guest.HostMemory} {ws bs : BitVec 64}
    (entry : Entry source ws bs) : source.memaddrs (ws+24#64) := by
  simpa only [byteAddress] using AllocatedBytes.word_mapped source ws 40 24 entry.environment.keccak.domain
    entry.wsArena (by decide) entry.wsAligned (by decide)

end InitECandidate.Solver.Input.CurrentVerify.AccountLookup

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Entry.of_recorded
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Entry.of_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Entry.root_mapped

namespace InitECandidate.Solver.Input.CurrentVerify.AccountLookup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- A real allocator changes the heap global while retaining the original
lookup workspace and trie. Its advanced bounded heap is supplied separately. -/
theorem Entry.of_heap_fields {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {ws bs : BitVec 64}
    (entry : Entry source ws bs) (memory : target.memory=source.memory)
    (metadata : MemoryMetadata.erase {target with globals:=source.globals}=MemoryMetadata.erase source)
    (globals : HeapGlobals source target) (heap : NormalHeapEffects.AtLeast (bs.toNat+80) target) : Entry target ws bs := by
  have code:=MemoryMetadata.code metadata
  have domain:=MemoryMetadata.domain metadata
  have endian:=MemoryMetadata.endian metadata
  change target.code=source.code at code
  change target.memaddrs=source.memaddrs at domain
  change target.be=source.be at endian
  refine ⟨⟨⟨by rw [code]; exact entry.environment.keccak.installed,domain.trans entry.environment.keccak.domain,
    (globals _ (by decide)).trans entry.environment.keccak.stateGlobal,(globals _ (by decide)).trans entry.environment.keccak.padGlobal,
    entry.environment.keccak.stateArena,entry.environment.keccak.padArena,entry.environment.keccak.stateAligned,entry.environment.keccak.padAligned⟩,
    endian.trans entry.environment.little,(globals _ (by decide)).trans entry.environment.nibbles,
    ⟨(globals _ (by decide)).trans entry.environment.arena.scratch,(globals _ (by decide)).trans entry.environment.arena.frame,
      domain.trans entry.environment.arena.domain,by rw [code]; exact entry.environment.arena.code⟩⟩,
    (globals _ (by decide)).trans entry.wsCell,entry.wsArena,entry.wsAligned,entry.lower,entry.wsBeforeBs,heap,?_⟩
  obtain ⟨db,node,dbBefore,stored,registry,member⟩:=entry.world
  obtain ⟨graph,validEq,regions,disjoint,⟨values⟩⟩:=registry.graph.after_agreement source target 1024 (ws.toNat+40) bs.toNat (Mpt.WitnessCore.WitnessValue db)
    registry.values registry.regions registry.disjoint domain (fun _ _=>congrFun memory _) (fun _ _=>congrFun memory _)
  refine ⟨db,node,dbBefore,(congrFun memory _).trans stored,⟨graph,values,regions,disjoint⟩,?_⟩
  change graph.valid node
  rw [validEq]
  exact member

namespace Leaf

def body : ProgHOL 64:=match Guest.Software.guestFn_ws_account_leaf with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "addr",.one)]
def hashArguments : List (ExpHOL 64):=[localVar "addr",.const 20#64,localVar "h"]
def hash : ProgHOL 64:=.call (some (none,none)) (ofString "keccak256") hashArguments
def lookupArguments : List (ExpHOL 64):=[.load .one (.op .add [.var .global (ofString "ws"),.const 24#64]),localVar "h"]
def finish : ProgHOL 64:=.seq (.call (some (none,none)) (ofString "heap_release") [localVar "mark"]) (.return (localVar "r"))
def lookup : ProgHOL 64:=.decCall (ofString "r") Mpt.TrieWalk.resultShape (ofString "trie_lookup") lookupArguments finish
def afterAlloc : ProgHOL 64:=.seq hash lookup
def afterMark : ProgHOL 64:=.decCall (ofString "h") .one (ofString "alloc") [.const 32#64] afterAlloc

theorem body_shape : body=.decCall (ofString "mark") .one (ofString "heap_mark") [] afterMark := by
  simp only [body,afterMark,afterAlloc,hash,hashArguments,lookup,lookupArguments,finish,Mpt.TrieWalk.resultShape,
    Guest.Software.guestFn_ws_account_leaf,progToHOL,expToHOL,shapeToHOL,localVar,List.map_cons,List.map_nil,Option.map_none]

theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "ws_account_leaf")=some (formals,body,Mpt.TrieWalk.resultShape) := by
  have found:=OriginalCode.indexed code installed 331 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_ws_account_leaf) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,Mpt.TrieWalk.resultShape,
    Guest.Software.guestFn_ws_account_leaf,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using found

theorem hash_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (address out : BitVec 64)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word address)))
    (outCell : source.locals.lookup (ofString "h")=some (.val (.word out))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) hashArguments=some (CurrentKeccak.Hash.values address out 20) := by
  simp [hashArguments,CurrentKeccak.Hash.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,addressCell,outCell]

theorem finish_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code finish 1 :=
  ClockCost.sequence code _ _ 1 0 (HeapScope.release_call_cost code installed (some none) _) (ClockCost.returned code _)

/-- Normal hashing preserves the real initialized trie, all value fields,
its WS root and heap. The temporary output is freshly beyond BS. -/
theorem hash_after {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {ws bs address out : BitVec 64}
    (entry : Entry source ws bs) (arena : AllocatedBytes.Arena out 32) (aligned : out.toNat%8=0) (fresh : bs.toNat≤out.toNat)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) hashArguments=some (CurrentKeccak.Hash.values address out 20))
    (normal : evaluateHOLFiniteState source hash=(none,post)) : Entry post ws bs := by
  have fields:=evaluation_fields source post hash none normal
  have globals (key : MlS) : post.globals.lookup key=source.globals.lookup key:=by
    have kept:=CurrentKeccak.Hash.call_globals key source.code entry.environment.keccak.installed hashArguments source rfl
    change GlobalEffects.erase key (evaluateHOLFiniteState source hash).2=GlobalEffects.erase key source at kept
    rw [normal] at kept
    exact congrArg Prod.snd kept
  have memory (query : BitVec 64) (lower : ws.toNat≤query.toNat) (upper : query.toNat<bs.toNat) : post.memory query=source.memory query:=by
    have stateAway:=CopyGeneral.Away.before 2701132160#64 query 200 2701132360 (by decide) (by decide) (by have low:=entry.lower; omega)
    have padAway:=CopyGeneral.Away.before 2701132360#64 query 136 2701132496 (by decide) (by decide) (by have low:=entry.lower; omega)
    have outAway:=CopyGeneral.Away.after out query 32 aligned (by have bound:=arena.upper; omega) (by omega)
    exact (CurrentKeccak.Hash.call_span_frame source post 2701132160#64 2701132360#64 address out query 20
      entry.environment.keccak hashArguments args (by decide) arena stateAway padAway outAway normal).memory
  have nextEnvironment : Environment post:=⟨entry.environment.keccak.after hash none
    (fun key=>CurrentKeccak.Hash.call_globals key source.code entry.environment.keccak.installed hashArguments) normal,
    fields.2.1.trans entry.environment.little,(globals _).trans entry.environment.nibbles,
    ⟨(globals _).trans entry.environment.arena.scratch,(globals _).trans entry.environment.arena.frame,
      fields.1.trans entry.environment.arena.domain,by rw [fields.2.2.2]; exact entry.environment.arena.code⟩⟩
  obtain ⟨heap,cell,lower,bounded,heapAligned⟩:=entry.heap
  refine ⟨nextEnvironment,(globals _).trans entry.wsCell,entry.wsArena,entry.wsAligned,entry.lower,entry.wsBeforeBs,
    ⟨heap,(globals _).trans cell,lower,bounded,heapAligned⟩,?_⟩
  obtain ⟨db,node,dbBefore,stored,registry,member⟩:=entry.world
  have agree : ∀ query,registry.graph.Footprint query→post.memory query=source.memory query:=by
    intro query required
    have bounds:=registry.graph.footprint_bounds (ws.toNat+40) bs.toNat registry.regions query required
    exact memory query (by omega) bounds.2
  have valueAgree : ∀ query,Mpt.TrieWalk.ValueFootprint registry.graph query→post.memory query=source.memory query:=by
    intro query required
    have bounds:=registry.graph.value_bounds (ws.toNat+40) bs.toNat registry.regions query required
    exact memory query (by omega) bounds.2
  obtain ⟨graph,validEq,regions,disjoint,⟨values⟩⟩:=registry.graph.after_agreement source post 1024 (ws.toNat+40) bs.toNat (Mpt.WitnessCore.WitnessValue db)
    registry.values registry.regions registry.disjoint fields.1 agree valueAgree
  have number : (ws+24#64).toNat=ws.toNat+24:=byteAddress_toNat ws 24 (by have bound:=entry.wsArena.upper; omega)
  refine ⟨db,node,dbBefore,(memory (ws+24#64) (by rw [number]; omega) (by rw [number]; have before:=entry.wsBeforeBs; omega)).trans stored,
    ⟨graph,values,regions,disjoint⟩,?_⟩
  change graph.valid node
  rw [validEq]
  exact member

/-- The original lookup/release suffix is priced using its actual initialized
trie and the mapped temporary digest allocation. -/
theorem lookup_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ws bs out : BitVec 64)
    (entry : Entry source ws bs) (arena : AllocatedBytes.Arena out 32) (fresh : bs.toNat≤out.toNat)
    (outCell : source.locals.lookup (ofString "h")=some (.val (.word out))) :
    source.clock-(evaluateHOLFiniteState source lookup).2.clock≤2092 := by
  obtain ⟨db,node,dbBefore,stored,registry,member⟩:=entry.world
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) lookupArguments=some (Mpt.TrieLookup.values node out):=by
    simp [lookupArguments,Mpt.TrieLookup.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,entry.wsCell,
      entry.root_mapped,stored,outCell,valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact]
  have protectedGraph : registry.graph.Protected 2701134704#64:=by
    intro query required offset inside
    have lower:=(registry.graph.footprint_bounds (ws.toNat+40) bs.toNat registry.regions query required).1
    exact (CopyGeneral.Away.before 2701134704#64 query 64 2701134768 (by decide) (by decide)
      (by have floor:=entry.lower; omega) offset inside).2
  have separate : ∀ left<32,∀ right<64,byteAddress out left≠byteAddress 2701134704#64 right:=by
    intro left leftInside right rightInside same
    have lhs:=byteAddress_toNat out left (by have bound:=arena.upper; omega)
    have rhs:=byteAddress_toNat 2701134704#64 right (by change 2701134704+right<2^64; omega)
    have equal:=congrArg BitVec.toNat same
    have lower:=entry.lower
    have before:=entry.wsBeforeBs
    change (byteAddress 2701134704#64 right).toNat=2701134704+right at rhs
    omega
  exact Mpt.TrieLookup.scoped_cost source node out 2701134704#64 registry.graph member protectedGraph entry.environment.nibbles
    entry.environment.little (by decide)
    (fun offset inside=>AllocatedBytes.byte_mapped source out 32 offset entry.environment.keccak.domain arena inside)
    (fun offset inside=>AllocatedBytes.byte_mapped source 2701134704#64 64 offset entry.environment.keccak.domain ⟨by decide,by decide⟩ inside)
    separate (ofString "r") lookupArguments finish 1 args entry.environment.keccak.installed (finish_cost source.code entry.environment.keccak.installed)

/-- The real software hash is bounded on all outcomes, including bad address
reads. Only its observed normal continuation supplies the preserved trie. -/
theorem after_alloc_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ws bs address out : BitVec 64)
    (entry : Entry source ws bs) (arena : AllocatedBytes.Arena out 32) (aligned : out.toNat%8=0) (fresh : bs.toNat≤out.toNat)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word address)))
    (outCell : source.locals.lookup (ofString "h")=some (.val (.word out))) :
    source.clock-(evaluateHOLFiniteState source afterAlloc).2.clock≤2782 := by
  have args:=hash_arguments source address out addressCell outCell
  have hashPrice:=CurrentKeccak.Hash.call_cost source hashArguments address out 20 (by decide) entry.environment.keccak.installed args
  change source.clock-(evaluateHOLFiniteState source hash).2.clock≤690 at hashPrice
  have hashClock:=evaluateHOLFiniteState_clock_le source hash
  rw [afterAlloc,evaluateHOLFiniteState_seq_line780]
  generalize observed : evaluateHOLFiniteState source hash=output at hashPrice hashClock ⊢
  obtain ⟨result,current⟩:=output
  change source.clock-current.clock≤690 at hashPrice
  change current.clock≤source.clock at hashClock
  cases result with
  | none=>
    have next:=hash_after entry arena aligned fresh args observed
    have currentOut : current.locals.lookup (ofString "h")=some (.val (.word out)):=
      (CallNormal.ignored_lookup source current (ofString "h") (ofString "keccak256") hashArguments observed).trans outCell
    have priced:=lookup_cost current ws bs out next arena fresh currentOut
    have forward:=evaluateHOLFiniteState_clock_le current lookup
    change source.clock-(evaluateHOLFiniteState current lookup).2.clock≤2782
    omega
  | some result=>
    change source.clock-current.clock≤2782
    omega

end Leaf
end InitECandidate.Solver.Input.CurrentVerify.AccountLookup

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Entry.of_heap_fields
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf.body_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf.original_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf.hash_arguments
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf.finish_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf.hash_after
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf.lookup_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf.after_alloc_cost

namespace InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Exact actual allocation continuation, shared by its cost and normal
result proofs. Room comes from that same allocator's observed guard. -/
theorem allocated_entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ws bs heap : BitVec 64)
    (entry : Entry source ws bs) (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (room : heap.toNat+32≤2952790016) :
    Entry (bind (PersistentAlloc.post {source with clock:=source.clock-1} heap 32#64) "h" heap) ws bs ∧
      AllocatedBytes.Arena heap 32 ∧ heap.toNat%8=0 ∧ bs.toNat≤heap.toNat := by
  obtain ⟨old,oldCell,afterBs,bounded,aligned⟩:=entry.heap
  have same : old=heap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (oldCell.symm.trans heapCell)))
  subst old
  let ready:=bind (PersistentAlloc.post {source with clock:=source.clock-1} heap 32#64) "h" heap
  have guards:=PersistentAlloc.guards heap 32#64 room
  have grows : heap.toNat+32≤(PersistentAlloc.rounded heap 32#64).toNat:=guards.2.2.1
  have globals : HeapGlobals source ready:=HeapGlobals.update source (PersistentAlloc.rounded heap 32#64)
  have cell : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 32#64))):=by
    simp [ready,PersistentAlloc.post,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have nextHeap : NormalHeapEffects.AtLeast (bs.toNat+80) ready:=
    ⟨PersistentAlloc.rounded heap 32#64,cell,by omega,guards.2.2.2.1,guards.2.2.2.2⟩
  exact ⟨entry.of_heap_fields rfl rfl globals nextHeap,
    ⟨by have floor:=entry.lower; have before:=entry.wsBeforeBs; omega,by omega⟩,aligned,by omega⟩

/-- The allocator's own normal return establishes room for the temporary
32byte digest. Failed allocations remain bounded stopped outcomes. -/
theorem after_mark_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ws bs address : BitVec 64)
    (entry : Entry source ws bs) (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word address))) :
    source.clock-(evaluateHOLFiniteState source afterMark).2.clock≤2783 := by
  obtain ⟨heap,heapCell,afterBs,bounded,aligned⟩:=entry.heap
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [.const 32#64]=some (PersistentAlloc.values 32#64):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,PersistentAlloc.values]
  generalize observed : evaluateHOLFiniteState source afterMark=output
  obtain ⟨result,target⟩:=output
  change source.clock-target.clock≤2783
  rcases CurrentAlloc.scoped_classified source target "h" [.const 32#64] afterAlloc heap 32#64 args entry.environment.keccak.installed heapCell bounded result observed with stopped|reached
  · omega
  · obtain ⟨funded,room,inner,continued,endpoint⟩:=reached
    let ready:=bind (PersistentAlloc.post {source with clock:=source.clock-1} heap 32#64) "h" heap
    obtain ⟨nextEntry,arena,outAligned,fresh⟩:=allocated_entry source ws bs heap entry heapCell room
    have currentAddress : ready.locals.lookup (ofString "addr")=some (.val (.word address)):=
      (bind_lookup_other _ "h" "addr" heap (by decide)).trans addressCell
    have currentOut : ready.locals.lookup (ofString "h")=some (.val (.word heap)):=bind_lookup_same _ _ _
    have price:=after_alloc_cost ready ws bs address heap nextEntry arena outAligned fresh currentAddress currentOut
    change evaluateHOLFiniteState ready afterAlloc=(result,inner) at continued
    rw [continued] at price
    change source.clock-1-inner.clock≤2782 at price
    rw [endpoint]
    change source.clock-inner.clock≤2783
    omega

/-- Complete current Software ws_account_leaf, including actual mark,
allocation guards, software hashing, bounded initialized-trie lookup and
release. All outcomes are retained and no later success is an entry fact. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ws bs address : BitVec 64)
    (entry : Entry source ws bs) (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word address))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤2784 := by
  by_cases zero : source.clock=0
  · omega
  have funded : 1≤source.clock:=by omega
  obtain ⟨heap,heapCell,afterBs,bounded,aligned⟩:=entry.heap
  let ready:=bind {source with clock:=source.clock-1} "mark" heap
  have nextEntry : Entry ready ws bs:=entry.of_frame rfl
  have currentAddress : ready.locals.lookup (ofString "addr")=some (.val (.word address)):=
    (bind_lookup_other _ "mark" "addr" heap (by decide)).trans addressCell
  have priced:=after_mark_cost ready ws bs address nextEntry currentAddress
  have actual:=HeapScope.mark_call_execute source heap "mark" afterMark heapCell (HeapScope.mark_original_code source.code entry.environment.keccak.installed) funded
  rw [body_shape,actual]
  change source.clock-(evaluateHOLFiniteState ready afterMark).2.clock≤2784
  change source.clock-1-(evaluateHOLFiniteState ready afterMark).2.clock≤2783 at priced
  omega

end InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf.after_mark_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf.body_cost

namespace InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The actual original account-leaf caller on every outcome. Its physical
entry is derived from initialized records and retained startup workspace. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ws bs address : BitVec 64)
    (entry : Entry source ws bs) (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word address)]) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "ws_account_leaf") arguments)).2.clock≤2785 := by
  obtain ⟨callee,called,addressCell⟩:=word_environment source.code.lookup (ofString "ws_account_leaf") (ofString "addr") body Mpt.TrieWalk.resultShape address
    (original_code source.code entry.environment.keccak.installed)
  exact ClockCost.call_current source destination (ofString "ws_account_leaf") arguments _ body callee Mpt.TrieWalk.resultShape 2784 args called
    (body_cost (callEntryStateHOLFinite source callee) ws bs address (entry.of_frame rfl) addressCell)

end InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf.call_cost

namespace InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem finish_normal_value (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (answer returned : ValueHOL 64)
    (cell : source.locals.lookup (ofString "r")=some answer)
    (normal : evaluateHOLFiniteState source finish=(some (.returned returned),post)) : returned=answer := by
  have safe : LocalPrefix (ofString "r") (.call (some (none,none)) (ofString "heap_release") [localVar "mark"]):=
    .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,firstRun,tailRun,localEq⟩:=safe.normal_continue source post (.return (localVar "r")) returned normal
  have current : middle.locals.lookup (ofString "r")=some answer:=localEq.trans cell
  have read : eval middle (localVar "r")=some answer:=by simp [eval,localVar,evalHOLExact,toExact,current]
  have actual:=(return_normal middle post (localVar "r") returned tailRun).1
  exact (Option.some.inj (read.symm.trans actual)).symm

/-- A real normal lookup/release returns the genuine binary triple with
its bounded mapped payload and witness-value property. -/
theorem lookup_normal_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ws bs out : BitVec 64)
    (entry : Entry source ws bs) (arena : AllocatedBytes.Arena out 32) (fresh : bs.toNat≤out.toNat)
    (outCell : source.locals.lookup (ofString "h")=some (.val (.word out)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source lookup=(some (.returned returned),post)) :
    ∃ db target answer inner,db.toNat≤ws.toNat ∧
      Mpt.TrieWalk.Answer target.memaddrs 1024 (property:=Mpt.WitnessCore.WitnessValue db) answer ∧
      Mpt.KeyToNibbles.OutputFrame source target 2701134704#64 ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source target "r" answer) finish=(some (.returned returned),inner) ∧
      post=restore source "r" inner := by
  obtain ⟨db,node,dbBefore,stored,registry,member⟩:=entry.world
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) lookupArguments=some (Mpt.TrieLookup.values node out):=by
    simp [lookupArguments,Mpt.TrieLookup.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,entry.wsCell,
      entry.root_mapped,stored,outCell,valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact]
  have protectedGraph : registry.graph.Protected 2701134704#64:=by
    intro query required offset inside
    have lower:=(registry.graph.footprint_bounds (ws.toNat+40) bs.toNat registry.regions query required).1
    exact (CopyGeneral.Away.before 2701134704#64 query 64 2701134768 (by decide) (by decide)
      (by have floor:=entry.lower; omega) offset inside).2
  have protectedValues : Mpt.TrieWalk.ValueProtected registry.graph 2701134704#64:=by
    intro query required offset inside
    have lower:=(registry.graph.value_bounds (ws.toNat+40) bs.toNat registry.regions query required).1
    exact (CopyGeneral.Away.before 2701134704#64 query 64 2701134768 (by decide) (by decide)
      (by have floor:=entry.lower; omega) offset inside).2
  have separate : ∀ left<32,∀ right<64,byteAddress out left≠byteAddress 2701134704#64 right:=by
    intro left leftInside right rightInside same
    have lhs:=byteAddress_toNat out left (by have bound:=arena.upper; omega)
    have rhs:=byteAddress_toNat 2701134704#64 right (by change 2701134704+right<2^64; omega)
    have equal:=congrArg BitVec.toNat same
    have lower:=entry.lower
    have before:=entry.wsBeforeBs
    change (byteAddress 2701134704#64 right).toNat=2701134704+right at rhs
    omega
  obtain ⟨funded,target,answer,inner,result,upper,lower,frame,finishRun,restored⟩:=
    Mpt.TrieLookup.scoped_normal source post node out 2701134704#64 registry.graph 1024 registry.values member protectedGraph protectedValues
      entry.environment.nibbles entry.environment.little (by decide)
      (fun offset inside=>AllocatedBytes.byte_mapped source out 32 offset entry.environment.keccak.domain arena inside)
      (fun offset inside=>AllocatedBytes.byte_mapped source 2701134704#64 64 offset entry.environment.keccak.domain ⟨by decide,by decide⟩ inside)
      separate "r" lookupArguments finish args entry.environment.keccak.installed returned normal
  exact ⟨db,target,answer,inner,dbBefore,result,frame,finishRun,restored⟩

theorem lookup_normal_value (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ws bs out : BitVec 64)
    (entry : Entry source ws bs) (arena : AllocatedBytes.Arena out 32) (fresh : bs.toNat≤out.toNat)
    (outCell : source.locals.lookup (ofString "h")=some (.val (.word out)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source lookup=(some (.returned returned),post)) :
    ∃ db,db.toNat≤ws.toNat ∧ Mpt.TrieWalk.Answer post.memaddrs 1024 (property:=Mpt.WitnessCore.WitnessValue db) returned := by
  obtain ⟨db,target,answer,inner,dbBefore,result,frame,finishRun,restored⟩:=lookup_normal_trace source post ws bs out entry arena fresh outCell returned normal
  let ready:=CallNormal.continuationEntry source target "r" answer
  have cell : ready.locals.lookup (ofString "r")=some answer:=CallNormal.continuation_lookup_same source target "r" answer
  have returnedEq:=finish_normal_value ready inner answer returned cell finishRun
  have domain:=(evaluation_fields ready inner finish (some (.returned returned)) finishRun).1
  change inner.memaddrs=target.memaddrs at domain
  have postDomain : post.memaddrs=target.memaddrs:=by rw [restored]; exact domain
  refine ⟨db,dbBefore,?_⟩
  rw [postDomain,returnedEq]
  exact result

/-- The actual normal hash feeds that same initialized-trie lookup. No
normal child call or future binary answer is supplied at entry. -/
theorem after_alloc_normal_value (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ws bs address out : BitVec 64)
    (entry : Entry source ws bs) (arena : AllocatedBytes.Arena out 32) (aligned : out.toNat%8=0) (fresh : bs.toNat≤out.toNat)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word address)))
    (outCell : source.locals.lookup (ofString "h")=some (.val (.word out)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterAlloc=(some (.returned returned),post)) :
    ∃ db,db.toNat≤ws.toNat ∧ Mpt.TrieWalk.Answer post.memaddrs 1024 (property:=Mpt.WitnessCore.WitnessValue db) returned := by
  have safe : LocalPrefix (ofString "h") hash:=.call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨current,hashRun,lookupRun,localEq⟩:=safe.normal_continue source post lookup returned normal
  have args:=hash_arguments source address out addressCell outCell
  have next:=hash_after entry arena aligned fresh args hashRun
  exact lookup_normal_value current post ws bs out next arena fresh (localEq.trans outCell) returned lookupRun

end InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf.finish_normal_value
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf.lookup_normal_value
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf.after_alloc_normal_value

namespace InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- A genuine normal allocation continuation retains the actual bounded
lookup answer through restoration of the digest pointer's local scope. -/
theorem after_mark_normal_value (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ws bs address : BitVec 64)
    (entry : Entry source ws bs) (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word address)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterMark=(some (.returned returned),post)) :
    ∃ db,db.toNat≤ws.toNat ∧ Mpt.TrieWalk.Answer post.memaddrs 1024 (property:=Mpt.WitnessCore.WitnessValue db) returned := by
  obtain ⟨heap,heapCell,afterBs,bounded,aligned⟩:=entry.heap
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [.const 32#64]=some (PersistentAlloc.values 32#64):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,PersistentAlloc.values]
  rcases CurrentAlloc.scoped_classified source post "h" [.const 32#64] afterAlloc heap 32#64 args entry.environment.keccak.installed heapCell bounded _ normal with stopped|reached
  · exact (stopped.2 returned rfl).elim
  · obtain ⟨funded,room,inner,continued,endpoint⟩:=reached
    let ready:=bind (PersistentAlloc.post {source with clock:=source.clock-1} heap 32#64) "h" heap
    obtain ⟨nextEntry,arena,outAligned,fresh⟩:=allocated_entry source ws bs heap entry heapCell room
    have currentAddress : ready.locals.lookup (ofString "addr")=some (.val (.word address)):=
      (bind_lookup_other _ "h" "addr" heap (by decide)).trans addressCell
    have currentOut : ready.locals.lookup (ofString "h")=some (.val (.word heap)):=bind_lookup_same _ _ _
    obtain ⟨db,dbBefore,answer⟩:=after_alloc_normal_value ready inner ws bs address heap nextEntry arena outAligned fresh currentAddress currentOut returned continued
    refine ⟨db,dbBefore,?_⟩
    rw [endpoint]
    exact answer

/-- Complete actual current account-leaf normal result. Both normal
allocation and hash execution are extracted from this same full run. -/
theorem body_normal_value (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ws bs address : BitVec 64)
    (entry : Entry source ws bs) (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word address)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    ∃ db,db.toNat≤ws.toNat ∧ Mpt.TrieWalk.Answer post.memaddrs 1024 (property:=Mpt.WitnessCore.WitnessValue db) returned := by
  rw [body_shape] at normal
  have funded:=CallNormal.normal_clock source post (ofString "mark") .one (ofString "heap_mark") [] afterMark returned normal
  obtain ⟨heap,heapCell,afterBs,bounded,aligned⟩:=entry.heap
  let ready:=bind {source with clock:=source.clock-1} "mark" heap
  let inner:=(evaluateHOLFiniteState ready afterMark).2
  have actual:=HeapScope.mark_call_execute source heap "mark" afterMark heapCell (HeapScope.mark_original_code source.code entry.environment.keccak.installed) funded
  have joined:=actual.symm.trans normal
  have resultEq:=congrArg Prod.fst joined
  change (evaluateHOLFiniteState ready afterMark).1=some (.returned returned) at resultEq
  have innerRun : evaluateHOLFiniteState ready afterMark=(some (.returned returned),inner):=Prod.ext resultEq rfl
  have postEq:=(congrArg Prod.snd joined).symm
  change post=restore source "mark" inner at postEq
  have nextEntry : Entry ready ws bs:=entry.of_frame rfl
  have currentAddress : ready.locals.lookup (ofString "addr")=some (.val (.word address)):=
    (bind_lookup_other _ "mark" "addr" heap (by decide)).trans addressCell
  obtain ⟨db,dbBefore,answer⟩:=after_mark_normal_value ready inner ws bs address nextEntry currentAddress returned innerRun
  refine ⟨db,dbBefore,?_⟩
  rw [postEq]
  exact answer

end InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf.allocated_entry
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf.after_mark_normal_value
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf.body_normal_value

namespace InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The genuine scoped caller either stops within2785ticks or reaches its
original continuation with the actual bounded lookup answer. The future
continuation is unrestricted and no successful caller outcome is assumed. -/
theorem scoped_classified (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ws bs address : BitVec 64)
    (entry : Entry source ws bs) (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word address)])
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) Mpt.TrieWalk.resultShape (ofString "ws_account_leaf") arguments continuation)=(result,post)) :
    (source.clock-post.clock≤2785 ∧ ∀ value,result≠some (.returned value)) ∨
      ∃ target answer inner db,Mpt.TrieWalk.Answer target.memaddrs 1024 (property:=Mpt.WitnessCore.WitnessValue db) answer ∧
        target.clock≤source.clock ∧ source.clock-target.clock≤2785 ∧
        evaluateHOLFiniteState (CallNormal.continuationEntry source target name answer) continuation=(result,inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called,addressCell⟩:=word_environment source.code.lookup (ofString "ws_account_leaf") (ofString "addr") body Mpt.TrieWalk.resultShape address
    (original_code source.code entry.environment.keccak.installed)
  have currentEntry : Entry (callEntryStateHOLFinite source callee) ws bs:=entry.of_frame rfl
  have price:=body_cost (callEntryStateHOLFinite source callee) ws bs address currentEntry addressCell
  rcases CallNormal.scoped_classified source post name Mpt.TrieWalk.resultShape (ofString "ws_account_leaf") arguments _ body continuation callee Mpt.TrieWalk.resultShape
    2784 args called price result run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨target,answer,inner,funded,normal,checked,forward,cost,continued,endpoint⟩:=reached
    obtain ⟨db,dbBefore,actualAnswer⟩:=body_normal_value (callEntryStateHOLFinite source callee) target ws bs address currentEntry addressCell answer normal
    exact Or.inr ⟨target,answer,inner,db,actualAnswer,forward,cost,continued,endpoint⟩

end InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf

namespace InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def body : ProgHOL 64:=match Guest.Software.guestFn_ws_get_account_optional with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "addr",.one)]
def afterLeaf : ProgHOL 64:=match body with | .decCall _ _ _ _ rest=>rest | _=>.skip

theorem body_shape : body=.decCall (ofString "leaf") Mpt.TrieWalk.resultShape (ofString "ws_account_leaf") [localVar "addr"] afterLeaf := by
  simp only [body,afterLeaf,Mpt.TrieWalk.resultShape,Guest.Software.guestFn_ws_get_account_optional,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar]

theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "ws_get_account_optional")=some (formals,body,.one) := by
  have found:=OriginalCode.indexed code installed 332 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_ws_get_account_optional) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,formals,
    Guest.Software.guestFn_ws_get_account_optional,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using found

/-- The actual account-provider body reaches its original absence/decode
continuation using the fully priced current leaf caller and real result. -/
theorem leaf_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ws bs address : BitVec 64)
    (entry : Entry source ws bs) (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word address)))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(result,post)) :
    (source.clock-post.clock≤2785 ∧ ∀ value,result≠some (.returned value)) ∨
      ∃ target answer inner db,Mpt.TrieWalk.Answer target.memaddrs 1024 (property:=Mpt.WitnessCore.WitnessValue db) answer ∧
        target.clock≤source.clock ∧ source.clock-target.clock≤2785 ∧
        evaluateHOLFiniteState (CallNormal.continuationEntry source target "leaf" answer) afterLeaf=(result,inner) ∧ post=restore source "leaf" inner := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "addr"]=some [.val (.word address)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,addressCell]
  rw [body_shape] at run
  exact Leaf.scoped_classified source post ws bs address entry "leaf" [localVar "addr"] afterLeaf args result run

end InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf.scoped_classified
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional.body_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional.original_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional.leaf_trace

namespace InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem nibble_globals (key : MlS) (code) : GlobalEffects.Preserves key code Mpt.KeyToNibbles.body := by
  simp only [Mpt.KeyToNibbles.body,Guest.Software.guestFn_key_to_nibbles,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  repeat first
    | apply GlobalEffects.declared
    | apply GlobalEffects.sequence
    | apply GlobalEffects.loop
    | exact GlobalEffects.assign key code _ _
    | exact GlobalEffects.byte_store key code _ _
    | exact GlobalEffects.returned key code _

theorem lookup_globals (key : MlS) (code) (installed : OriginalCode.Installed code) : GlobalEffects.Preserves key code Mpt.TrieLookup.body := by
  rw [Mpt.TrieLookup.body_shape]
  unfold Mpt.TrieLookup.prepare Mpt.TrieLookup.forward
  exact GlobalEffects.sequence key code _ _
    (GlobalEffects.call_body key code (some none) (ofString "key_to_nibbles") _ Mpt.KeyToNibbles.formals Mpt.KeyToNibbles.body .one
      (Mpt.KeyToNibbles.original_code code installed) (nibble_globals key code))
    (GlobalEffects.call_body key code none (ofString "trie_walk") _ Mpt.TrieWalk.formals Mpt.TrieWalk.body Mpt.TrieWalk.resultShape
      (Mpt.TrieWalk.original_code code installed) (GlobalEffects.of_readonly key code _ (Mpt.TrieWalk.readonly code installed)))

/-- The actual software leaf may change heap_ptr temporarily. Every other
workspace/global cell survives every outcome of this unchanged body. -/
theorem nonheap_globals (key : MlS) (code) (installed : OriginalCode.Installed code) (other : key≠ofString "heap_ptr") :
    GlobalEffects.Preserves key code body := by
  have markPure : GlobalEffects.Preserves key code HeapScope.markBody:=by
    rw [HeapScope.mark_shape]; exact GlobalEffects.returned key code _
  have releasePure : GlobalEffects.Preserves key code HeapScope.releaseBody:=by
    rw [HeapScope.release_shape]
    exact GlobalEffects.sequence key code _ _ (GlobalEffects.global_other key code _ _ other) (GlobalEffects.returned key code _)
  rw [body_shape]
  unfold afterMark afterAlloc hash lookup finish
  repeat first
    | apply GlobalEffects.sequence
    | exact GlobalEffects.returned key code _
    | apply GlobalEffects.scoped_body key code (ofString "mark") .one (ofString "heap_mark") _ _ [] HeapScope.markBody .one
        (HeapScope.mark_original_code code installed) markPure
    | apply GlobalEffects.scoped_body key code (ofString "h") .one (ofString "alloc") _ _ PersistentAlloc.formals PersistentAlloc.body .one
        (PersistentAlloc.original_code code installed) (PersistentAlloc.globals key code installed other)
    | apply GlobalEffects.scoped_body key code (ofString "r") Mpt.TrieWalk.resultShape (ofString "trie_lookup") _ _ Mpt.TrieLookup.formals Mpt.TrieLookup.body Mpt.TrieWalk.resultShape
        (Mpt.TrieLookup.original_code code installed) (lookup_globals key code installed)
    | exact CurrentKeccak.Hash.call_globals key code installed hashArguments
    | exact GlobalEffects.call_body key code (some none) (ofString "heap_release") _ HeapScope.releaseFormals HeapScope.releaseBody .one
        (HeapScope.release_original_code code installed) releasePure

/-- The genuine release/return suffix restores its actual typed saved mark.
It neither assumes a future release nor compares that mark with the current heap. -/
theorem finish_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (mark old : BitVec 64)
    (markCell : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word old)))
    (installed : OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source finish=(some (.returned returned),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  have safe : LocalPrefix (ofString "r") (.call (some (none,none)) (ofString "heap_release") [localVar "mark"]):=
    .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,released,tailRun,locals⟩:=safe.normal_continue source post (.return (localVar "r")) returned normal
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "mark"]=some [.val (.word mark)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,markCell]
  have releaseEq:=HeapScope.release_normal source middle mark old [localVar "mark"] args heap installed released
  have postEq:=(return_normal middle post (localVar "r") returned tailRun).2
  rw [postEq,releaseEq]
  simp [HeapScope.releasePost,emptyLocalsHOLFinite,HolFiniteMapExact.update,FUPDATE]

/-- Hashing and nibble conversion preserve the current heap; the actual
following release therefore restores the saved mark on every normal return. -/
theorem after_alloc_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (mark old : BitVec 64)
    (markCell : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word old)))
    (installed : OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterAlloc=(some (.returned returned),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  have safe : LocalPrefix (ofString "mark") hash:=.call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,hashRun,lookupRun,markEq⟩:=safe.normal_continue source post lookup returned normal
  have globalFrame:=CurrentKeccak.Hash.call_globals (ofString "heap_ptr") source.code installed hashArguments source rfl
  change GlobalEffects.erase (ofString "heap_ptr") (evaluateHOLFiniteState source hash).2=GlobalEffects.erase (ofString "heap_ptr") source at globalFrame
  rw [hashRun] at globalFrame
  have middleHeap:=(congrArg Prod.snd globalFrame).trans heap
  have middleInstalled:=OriginalCode.after_execution source middle hash none hashRun installed
  have middleMark:=markEq.trans markCell
  obtain ⟨positive,actualValues,actualBody,callee,shape,target,answer,inner,args,called,bodyRun,checked,tailRun,restored⟩:=
    CallNormal.scoped_data middle post "r" Mpt.TrieWalk.resultShape (ofString "trie_lookup") lookupArguments finish returned lookupRun
  have bodyEq:=GlobalEffects.lookup_body middle.code (ofString "trie_lookup") Mpt.TrieLookup.formals Mpt.TrieLookup.body Mpt.TrieWalk.resultShape
    (Mpt.TrieLookup.original_code middle.code middleInstalled) actualValues actualBody callee shape called
  subst actualBody
  have frame:=lookup_globals (ofString "heap_ptr") middle.code middleInstalled (callEntryStateHOLFinite middle callee) rfl
  rw [bodyRun] at frame
  let ready:=CallNormal.continuationEntry middle target "r" answer
  have readyMark : ready.locals.lookup (ofString "mark")=some (.val (.word mark)):=
    (CallNormal.continuation_lookup_other middle target "r" "mark" answer (by decide)).trans middleMark
  have readyHeap : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word old)):=(congrArg Prod.snd frame).trans middleHeap
  have readyInstalled:=OriginalCode.after_execution (callEntryStateHOLFinite middle callee) target Mpt.TrieLookup.body _ bodyRun middleInstalled
  have restoredHeap:=finish_heap ready inner mark old readyMark readyHeap readyInstalled returned tailRun
  rw [restored]
  exact restoredHeap

theorem after_mark_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (mark heap : BitVec 64)
    (markCell : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (bounded : heap.toNat≤2952790016) (installed : OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterMark=(some (.returned returned),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [.const 32#64]=some (PersistentAlloc.values 32#64):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,PersistentAlloc.values]
  rcases CurrentAlloc.scoped_classified source post "h" [.const 32#64] afterAlloc heap 32#64 args installed heapCell bounded _ normal with stopped|reached
  · exact (stopped.2 returned rfl).elim
  · obtain ⟨funded,room,inner,continued,endpoint⟩:=reached
    let ready:=bind (PersistentAlloc.post {source with clock:=source.clock-1} heap 32#64) "h" heap
    have currentMark : ready.locals.lookup (ofString "mark")=some (.val (.word mark)):=
      (bind_lookup_other _ "h" "mark" heap (by decide)).trans markCell
    have currentHeap : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 32#64))):=by
      simp [ready,PersistentAlloc.post,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
    have restoredHeap:=after_alloc_heap ready inner mark (PersistentAlloc.rounded heap 32#64) currentMark currentHeap installed returned continued
    rw [endpoint]
    exact restoredHeap

/-- The complete actual leaf restores its original heap after temporary
hashing and lookup, as derived from the observed normal call itself. -/
theorem body_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (bounded : heap.toNat≤2952790016) (installed : OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) := by
  rw [body_shape] at normal
  have funded:=CallNormal.normal_clock source post (ofString "mark") .one (ofString "heap_mark") [] afterMark returned normal
  let ready:=bind {source with clock:=source.clock-1} "mark" heap
  let inner:=(evaluateHOLFiniteState ready afterMark).2
  have actual:=HeapScope.mark_call_execute source heap "mark" afterMark heapCell (HeapScope.mark_original_code source.code installed) funded
  have joined:=actual.symm.trans normal
  have resultEq:=congrArg Prod.fst joined
  change (evaluateHOLFiniteState ready afterMark).1=some (.returned returned) at resultEq
  have innerRun : evaluateHOLFiniteState ready afterMark=(some (.returned returned),inner):=Prod.ext resultEq rfl
  have postEq:=(congrArg Prod.snd joined).symm
  change post=restore source "mark" inner at postEq
  have restoredHeap:=after_mark_heap ready inner heap heap (bind_lookup_same _ _ _) heapCell bounded installed returned innerRun
  rw [postEq]
  exact restoredHeap

end InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf.nibble_globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf.lookup_globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf.nonheap_globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf.finish_heap
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf.after_alloc_heap
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf.after_mark_heap
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf.body_heap

namespace InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Complete actual leaf execution retains the real main scratch cursors,
hash workspaces and endian, even when it stops before returning. -/
theorem environment_after {source post : PanSemStateFiniteExact 64 Guest.HostMemory} (ready : Environment source)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(result,post)) : Environment post := by
  have fields:=evaluation_fields source post body result run
  have globals (key : MlS) (other : key≠ofString "heap_ptr") : post.globals.lookup key=source.globals.lookup key:=by
    have frame:=nonheap_globals key source.code ready.keccak.installed other source rfl
    rw [run] at frame
    exact congrArg Prod.snd frame
  exact ⟨⟨by rw [fields.2.2.2]; exact ready.keccak.installed,fields.1.trans ready.keccak.domain,
    (globals _ (by decide)).trans ready.keccak.stateGlobal,(globals _ (by decide)).trans ready.keccak.padGlobal,
    ready.keccak.stateArena,ready.keccak.padArena,ready.keccak.stateAligned,ready.keccak.padAligned⟩,
    fields.2.1.trans ready.little,(globals _ (by decide)).trans ready.nibbles,
    ⟨(globals _ (by decide)).trans ready.arena.scratch,(globals _ (by decide)).trans ready.arena.frame,
      fields.1.trans ready.arena.domain,by rw [fields.2.2.2]; exact ready.arena.code⟩⟩

/-- Both current heap and startup workspace at the provider continuation
come from this real scoped leaf invocation. Its normal result is still the
same actual bounded trie answer, rather than a later lookup hypothesis. -/
theorem scoped_complete (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ws bs address : BitVec 64)
    (entry : Entry source ws bs) (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word address)])
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) Mpt.TrieWalk.resultShape (ofString "ws_account_leaf") arguments continuation)=(result,post)) :
    (source.clock-post.clock≤2785 ∧ ∀ value,result≠some (.returned value)) ∨
      ∃ target answer inner db,db.toNat≤ws.toNat ∧ Mpt.TrieWalk.Answer target.memaddrs 1024 (property:=Mpt.WitnessCore.WitnessValue db) answer ∧
        Environment target ∧ NormalHeapEffects.AtLeast (bs.toNat+80) target ∧
        target.clock≤source.clock ∧ source.clock-target.clock≤2785 ∧
        evaluateHOLFiniteState (CallNormal.continuationEntry source target name answer) continuation=(result,inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called,addressCell⟩:=word_environment source.code.lookup (ofString "ws_account_leaf") (ofString "addr") body Mpt.TrieWalk.resultShape address
    (original_code source.code entry.environment.keccak.installed)
  have currentEntry : Entry (callEntryStateHOLFinite source callee) ws bs:=entry.of_frame rfl
  have price:=body_cost (callEntryStateHOLFinite source callee) ws bs address currentEntry addressCell
  rcases CallNormal.scoped_classified source post name Mpt.TrieWalk.resultShape (ofString "ws_account_leaf") arguments _ body continuation callee Mpt.TrieWalk.resultShape
    2784 args called price result run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨target,answer,inner,funded,normal,checked,forward,cost,continued,endpoint⟩:=reached
    obtain ⟨db,dbBefore,actualAnswer⟩:=body_normal_value (callEntryStateHOLFinite source callee) target ws bs address currentEntry addressCell answer normal
    have environment:=environment_after currentEntry.environment _ normal
    obtain ⟨heap,heapCell,lower,bounded,aligned⟩:=entry.heap
    have restoredHeap:=body_heap (callEntryStateHOLFinite source callee) target heap heapCell bounded entry.environment.keccak.installed answer normal
    exact Or.inr ⟨target,answer,inner,db,dbBefore,actualAnswer,environment,⟨heap,restoredHeap,lower,bounded,aligned⟩,forward,cost,continued,endpoint⟩

end InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf.environment_after
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf.scoped_complete

namespace InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The original provider's actual absence/decode continuation. Every
nonempty payload precedes WS and hence the restored current heap; the
main scratch cursors are retained independently of those payload bytes. -/
structure Ready (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ws bs : BitVec 64) : Prop where
  environment : Environment source
  heap : NormalHeapEffects.AtLeast (bs.toNat+80) source
  wsBeforeBs : ws.toNat+40≤bs.toNat
  lower : 2701135464≤ws.toNat
  leaf : ∃ answer,source.locals.lookup (ofString "leaf")=some answer ∧
    Mpt.TrieWalk.Answer source.memaddrs 1024 (property:=Mpt.WitnessCore.WitnessValue ws) answer

/-- Strengthened real provider trace, with initialized value bounds,
actual restored heap, unchanged startup scratch and original continuation. -/
theorem leaf_trace_ready (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ws bs address : BitVec 64)
    (entry : Entry source ws bs) (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word address)))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(result,post)) :
    (source.clock-post.clock≤2785 ∧ ∀ value,result≠some (.returned value)) ∨
      ∃ current inner,Ready current ws bs ∧ current.clock≤source.clock ∧ source.clock-current.clock≤2785 ∧
        CallPrefix.ScopeFrame post inner ∧ evaluateHOLFiniteState current afterLeaf=(result,inner) := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "addr"]=some [.val (.word address)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,addressCell]
  rw [body_shape] at run
  rcases Leaf.scoped_complete source post ws bs address entry "leaf" [localVar "addr"] afterLeaf args result run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨target,answer,inner,db,dbBefore,actualAnswer,environment,heap,forward,cost,continued,endpoint⟩:=reached
    let current:=CallNormal.continuationEntry source target "leaf" answer
    have currentEnvironment : Environment current:=environment.of_metadata rfl
    have currentHeap : NormalHeapEffects.AtLeast (bs.toNat+80) current:=heap
    have boundedAnswer : Mpt.TrieWalk.Answer current.memaddrs 1024 (property:=Mpt.WitnessCore.WitnessValue ws) answer:=by
      rcases actualAnswer with absent|present
      · exact Or.inl absent
      · obtain ⟨pointer,length,equal,payload,property⟩:=present
        refine Or.inr ⟨pointer,length,equal,payload,?_⟩
        rcases property with empty|bounded
        · exact Or.inl empty
        · exact Or.inr ⟨bounded.1,Nat.le_trans bounded.2 dbBefore⟩
    have ready : Ready current ws bs:=⟨currentEnvironment,currentHeap,entry.wsBeforeBs,entry.lower,
      answer,CallNormal.continuation_lookup_same source target "leaf" answer,boundedAnswer⟩
    exact Or.inr ⟨current,inner,ready,forward,cost,(by rw [endpoint]; exact ⟨rfl,rfl⟩),continued⟩

/-- Nonempty initialized payloads are entirely before the current heap.
The zero-length case remains explicit, since the decoder must reject it
from its own length guard without an invented pointer-order premise. -/
theorem Ready.payload_before_heap {source : PanSemStateFiniteExact 64 Guest.HostMemory} {ws bs pointer length heap : BitVec 64}
    (ready : Ready source ws bs) (property : Mpt.WitnessCore.WitnessValue ws pointer length)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) :
    length=0#64 ∨ (2701131776≤pointer.toNat ∧ pointer.toNat+length.toNat≤heap.toNat) := by
  rcases property with empty|bounded
  · exact Or.inl empty
  · obtain ⟨actual,cell,lower,upper,aligned⟩:=ready.heap
    have same : actual=heap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (cell.symm.trans heapCell)))
    subst actual
    exact Or.inr ⟨bounded.1,Nat.le_trans bounded.2 (by have before:=ready.wsBeforeBs; omega)⟩

theorem Ready.live_arena {source : PanSemStateFiniteExact 64 Guest.HostMemory} {ws bs : BitVec 64}
    (ready : Ready source ws bs) : Rlp.LiveArena source := Rlp.LiveArena.of_startup ready.environment.arena

end InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional.leaf_trace_ready
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional.Ready.payload_before_heap
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional.Ready.live_arena

namespace InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def absentGuard : ProgHOL 64:=.ite (.cmp .equal (.rfield 0 (localVar "leaf")) (.const 0#64)) (.return (.const 1#64)) .skip
def afterGuard : ProgHOL 64:=match afterLeaf with | .seq _ rest=>rest | _=>.skip
def afterAlloc : ProgHOL 64:=match afterGuard with | .decCall _ _ _ _ rest=>rest | _=>.skip
def decodeArguments : List (ExpHOL 64):=[.rfield 1 (localVar "leaf"),.rfield 2 (localVar "leaf"),localVar "a"]
def decode : ProgHOL 64:=.call (some (none,none)) (ofString "decode_account_from_leaf") decodeArguments

theorem after_leaf_shape : afterLeaf=.seq absentGuard afterGuard := by
  simp only [afterLeaf,body,absentGuard,afterGuard,Guest.Software.guestFn_ws_get_account_optional,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar]

theorem after_guard_shape : afterGuard=.decCall (ofString "a") .one (ofString "alloc") [.const 56#64] afterAlloc := by
  simp only [afterGuard,afterLeaf,body,afterAlloc,Guest.Software.guestFn_ws_get_account_optional,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]

theorem after_alloc_shape : afterAlloc=.seq decode (.return (localVar "a")) := by
  simp only [afterAlloc,afterGuard,afterLeaf,body,decode,decodeArguments,Guest.Software.guestFn_ws_get_account_optional,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,localVar]

/-- The actual absent triple returns the original sentinel immediately,
without allocation, decoding or a source caller/loop tick. -/
theorem absent_after_leaf (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (leafCell : source.locals.lookup (ofString "leaf")=some (Mpt.TrieWalk.triple 0#64 0#64 0#64)) :
    evaluateHOLFiniteState source afterLeaf=(some (.returned (.val (.word 1#64))),emptyLocalsHOLFinite source) := by
  rw [after_leaf_shape,evaluateHOLFiniteState_seq_line780]
  simp [absentGuard,evaluateHOLFiniteState_ite,evalHOLExact,evalListHOLExact,localVar,toExact,leafCell,Mpt.TrieWalk.triple,
    valueIsWord,valueWord,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_return,shapeOfHOLExact,sizeOfShapeWithContextHOL]

/-- A real present triple reaches the original allocation/decoder suffix;
its guard changes no state and consumes no source caller/loop tick. -/
theorem present_after_leaf (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (leafCell : source.locals.lookup (ofString "leaf")=some (Mpt.TrieWalk.triple 1#64 pointer length)) :
    evaluateHOLFiniteState source afterLeaf=evaluateHOLFiniteState source afterGuard := by
  rw [after_leaf_shape,evaluateHOLFiniteState_seq_line780]
  simp [absentGuard,evaluateHOLFiniteState_ite,evalHOLExact,evalListHOLExact,localVar,toExact,leafCell,Mpt.TrieWalk.triple,
    valueIsWord,valueWord,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]

end InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional.after_leaf_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional.after_guard_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional.after_alloc_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional.absent_after_leaf
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional.present_after_leaf

namespace InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem after_alloc_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length heap out : BitVec 64)
    (leafCell : source.locals.lookup (ofString "leaf")=some (Mpt.TrieWalk.triple 1#64 pointer length))
    (outputCell : source.locals.lookup (ofString "a")=some (.val (.word out)))
    (arena : Rlp.LiveArena source) (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤2952790016) (before : length≠0#64→pointer.toNat+length.toNat≤heap.toNat)
    (sizeBound : 16*length.toNat<2^64) (output : Mpt.AccountDecode.Output out) :
    source.clock-(evaluateHOLFiniteState source afterAlloc).2.clock≤191*length.toNat+262 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) decodeArguments=some (Mpt.AccountDecode.values pointer length out):=by
    simp [decodeArguments,Mpt.AccountDecode.values,Mpt.TrieWalk.triple,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,leafCell,outputCell]
  have priced:=Mpt.AccountDecode.Current.call_cost source pointer length heap out arena heapCell heapBound before sizeBound output arena.code (some none) decodeArguments args
  rw [after_alloc_shape]
  simpa only [Nat.add_zero] using ClockCost.sequence_current source decode (.return (localVar "a")) (191*length.toNat+262) 0 priced (ClockCost.returned source.code _)

/-- Actual56byte allocation derives its own room and fresh account output.
Only the real normal branch invokes the complete current decoder bound. -/
theorem after_guard_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ws bs pointer length : BitVec 64)
    (ready : Ready source ws bs)
    (leafCell : source.locals.lookup (ofString "leaf")=some (Mpt.TrieWalk.triple 1#64 pointer length))
    (small : length.toNat≤1024) (property : Mpt.WitnessCore.WitnessValue ws pointer length) :
    source.clock-(evaluateHOLFiniteState source afterGuard).2.clock≤191*length.toNat+263 := by
  obtain ⟨heap,heapCell,afterBs,bounded,aligned⟩:=ready.heap
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [.const 56#64]=some (PersistentAlloc.values 56#64):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,PersistentAlloc.values]
  generalize observed : evaluateHOLFiniteState source afterGuard=result
  obtain ⟨outcome,post⟩:=result
  change source.clock-post.clock≤191*length.toNat+263
  rcases CurrentAlloc.scoped_classified source post "a" [.const 56#64] afterAlloc heap 56#64 args ready.environment.keccak.installed heapCell bounded outcome (by rw [←after_guard_shape]; exact observed) with stopped|reached
  · omega
  · obtain ⟨funded,room,inner,continued,endpoint⟩:=reached
    let current:=bind (PersistentAlloc.post {source with clock:=source.clock-1} heap 56#64) "a" heap
    have globals : HeapGlobals source current:=HeapGlobals.update source (PersistentAlloc.rounded heap 56#64)
    have currentStartup : CurrentStartup.ArenaState current:=
      ⟨(globals _ (by decide)).trans ready.environment.arena.scratch,(globals _ (by decide)).trans ready.environment.arena.frame,
        ready.environment.arena.domain,ready.environment.arena.code⟩
    have currentLeaf : current.locals.lookup (ofString "leaf")=some (Mpt.TrieWalk.triple 1#64 pointer length):=
      (bind_lookup_other _ "a" "leaf" heap (by decide)).trans leafCell
    have currentOutput : current.locals.lookup (ofString "a")=some (.val (.word heap)):=bind_lookup_same _ _ _
    have currentHeap : current.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 56#64))):=by
      simp [current,PersistentAlloc.post,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
    have guards:=PersistentAlloc.guards heap 56#64 room
    have grows : heap.toNat+56≤(PersistentAlloc.rounded heap 56#64).toNat:=guards.2.2.1
    have output : Mpt.AccountDecode.Output heap:=⟨by have lower:=ready.lower; have before:=ready.wsBeforeBs; omega,
      by change heap.toNat+56≤2952790016 at room; omega,aligned⟩
    have before : length≠0#64→pointer.toNat+length.toNat≤(PersistentAlloc.rounded heap 56#64).toNat:=by
      intro nonempty
      rcases property with empty|bounds
      · exact (nonempty empty).elim
      · have prior:=ready.wsBeforeBs; omega
    have priced:=after_alloc_cost current pointer length (PersistentAlloc.rounded heap 56#64) heap currentLeaf currentOutput
      (Rlp.LiveArena.of_startup currentStartup) currentHeap guards.2.2.2.1 before (by omega) output
    change evaluateHOLFiniteState current afterAlloc=(outcome,inner) at continued
    rw [continued] at priced
    change source.clock-1-inner.clock≤191*length.toNat+262 at priced
    rw [endpoint]
    change source.clock-inner.clock≤191*length.toNat+263
    omega

/-- The original absent/present guard, genuine allocation and complete
current decoder cover every actual provider continuation outcome. -/
theorem after_leaf_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ws bs : BitVec 64) (ready : Ready source ws bs) :
    source.clock-(evaluateHOLFiniteState source afterLeaf).2.clock≤195847 := by
  obtain ⟨answer,leafCell,result⟩:=ready.leaf
  rcases result with absent|present
  · rw [absent] at leafCell
    rw [absent_after_leaf source leafCell]
    change source.clock-source.clock≤195847
    omega
  · obtain ⟨pointer,length,valueEq,payload,property⟩:=present
    rw [valueEq] at leafCell
    rw [present_after_leaf source pointer length leafCell]
    have priced:=after_guard_cost source ws bs pointer length ready leafCell payload.1 property
    have small:=payload.1
    omega

/-- Complete actual unchanged ws_get_account_optional, including absent
sentinel, allocation failures, malformed RLP and all normal decoder outcomes. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ws bs address : BitVec 64)
    (entry : Entry source ws bs) (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word address))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤198632 := by
  generalize observed : evaluateHOLFiniteState source body=result
  obtain ⟨outcome,post⟩:=result
  change source.clock-post.clock≤198632
  rcases leaf_trace_ready source post ws bs address entry addressCell outcome observed with stopped|reached
  · omega
  · obtain ⟨current,inner,ready,forward,price,scope,continued⟩:=reached
    have tail:=after_leaf_cost current ws bs ready
    rw [continued] at tail
    change current.clock-inner.clock≤195847 at tail
    have endpoint:=scope.clock
    omega

theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ws bs address : BitVec 64)
    (entry : Entry source ws bs) (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word address)]) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "ws_get_account_optional") arguments)).2.clock≤198633 := by
  obtain ⟨callee,called,addressCell⟩:=word_environment source.code.lookup (ofString "ws_get_account_optional") (ofString "addr") body .one address
    (original_code source.code entry.environment.keccak.installed)
  exact ClockCost.call_current source destination (ofString "ws_get_account_optional") arguments _ body callee .one 198632 args called
    (body_cost (callEntryStateHOLFinite source callee) ws bs address (entry.of_frame rfl) addressCell)

end InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional.after_alloc_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional.after_guard_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional.after_leaf_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional.body_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional.call_cost

namespace InitECandidate.Solver.Input.CurrentVerify.PreStateAccount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem after_record_shape : afterRecord=.decCall (ofString "a") .one (ofString "ws_get_account_optional") [localVar "addr"] (.return (localVar "a")) := by
  simp only [afterRecord,afterMiss,afterGet,afterSet,body,Guest.Software.guestFn_get_pre_state_account_optional,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar]

/-- The unchanged workspace-provider call and literal return, supplied by
real initialized records and the actual preserved startup environment. -/
theorem after_record_cost {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {cutoff ws bs table record heap pointer : BitVec 64}
    (state : RecordPreStateRead.Recorded origin source cutoff ws bs table record heap)
    (ready : AccountLookup.Environment source)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word pointer))) :
    source.clock-(evaluateHOLFiniteState source afterRecord).2.clock≤198633 := by
  have entry:=AccountLookup.Entry.of_recorded state ready
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "addr"]=some [.val (.word pointer)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,addressCell]
  obtain ⟨callee,called,cell⟩:=word_environment source.code.lookup (ofString "ws_get_account_optional") (ofString "addr") AccountLookup.Optional.body .one pointer
    (AccountLookup.Optional.original_code source.code ready.keccak.installed)
  rw [after_record_shape]
  have priced:=ClockCost.scoped_current source (ofString "a") .one (ofString "ws_get_account_optional") [localVar "addr"] _ AccountLookup.Optional.body (.return (localVar "a")) callee .one
    198632 0 args called
    (AccountLookup.Optional.body_cost (callEntryStateHOLFinite source callee) ws bs pointer (entry.of_frame rfl) cell)
    (ClockCost.returned source.code _)
  exact priced

/-- Complete current first pre-state account getter, from the actual
fresh/access/initialized-record context. Cache miss, read recording and
workspace lookup/decoding all retain their stopped outcomes. -/
theorem body_cost {origin initialized source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {record cutoff ws bs heap access pointer : BitVec 64}
    (context : FreshTransaction.Context origin source record bs heap FreshTransaction.remainingTables)
    (state : AccountAccess.AccessState source record access)
    (records : RunAttempt.InitializedRecords initialized origin cutoff ws bs) (before : cutoff.toNat≤record.toNat)
    (ready : AccountLookup.Environment origin)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word pointer))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤198960 := by
  generalize observed : evaluateHOLFiniteState source body=result
  obtain ⟨outcome,post⟩:=result
  change source.clock-post.clock≤198960
  rcases to_after_record_environment context state records before ready addressCell outcome observed with stopped|reached
  · omega
  · obtain ⟨current,inner,table,last,lastEnvironment,lastAddress,forward,price,scope,continued⟩:=reached
    have tail:=after_record_cost last lastEnvironment lastAddress
    rw [continued] at tail
    change current.clock-inner.clock≤198633 at tail
    have endpoint:=scope.clock
    omega

theorem call_cost {origin initialized source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {record cutoff ws bs heap access : BitVec 64}
    (context : FreshTransaction.Context origin source record bs heap FreshTransaction.remainingTables)
    (state : AccountAccess.AccessState source record access)
    (records : RunAttempt.InitializedRecords initialized origin cutoff ws bs) (before : cutoff.toNat≤record.toNat)
    (ready : AccountLookup.Environment origin) (pointer : BitVec 64) (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word pointer)]) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "get_pre_state_account_optional") arguments)).2.clock≤198961 := by
  obtain ⟨callee,called,addressCell⟩:=word_environment source.code.lookup (ofString "get_pre_state_account_optional") (ofString "addr") body .one pointer
    (original_code source.code context.runtime.code)
  exact ClockCost.call_current source destination (ofString "get_pre_state_account_optional") arguments _ body callee .one 198960 args called
    (body_cost (context.of_erase rfl) (state.of_erase rfl) records before ready addressCell)

end InitECandidate.Solver.Input.CurrentVerify.PreStateAccount

#print axioms InitECandidate.Solver.Input.CurrentVerify.PreStateAccount.after_record_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.PreStateAccount.after_record_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.PreStateAccount.body_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.PreStateAccount.call_cost

namespace InitECandidate.Solver.Input.CurrentVerify.AccountAccess
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The actual miss suffix calls the pre-state provider and returns it.
This unchanged path does not insert anything into the account cache. -/
theorem after_miss_cost {origin initialized source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {record cutoff ws bs heap access pointer : BitVec 64}
    (context : FreshTransaction.Context origin source record bs heap FreshTransaction.remainingTables)
    (state : AccessState source record access)
    (records : RunAttempt.InitializedRecords initialized origin cutoff ws bs) (before : cutoff.toNat≤record.toNat)
    (ready : AccountLookup.Environment origin)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word pointer))) :
    source.clock-(evaluateHOLFiniteState source afterMiss).2.clock≤198961 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "addr"]=some [.val (.word pointer)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,addressCell]
  obtain ⟨callee,called,cell⟩:=word_environment source.code.lookup (ofString "get_pre_state_account_optional") (ofString "addr") PreStateAccount.body .one pointer
    (PreStateAccount.original_code source.code context.runtime.code)
  rw [miss_shapes.2]
  exact ClockCost.scoped_current source (ofString "a") .one (ofString "get_pre_state_account_optional") [localVar "addr"] _ PreStateAccount.body (.return (localVar "a")) callee .one
    198960 0 args called (PreStateAccount.body_cost (context.of_erase rfl) (state.of_erase rfl) records before ready cell) (ClockCost.returned source.code _)

/-- Complete first actual get_account_optional, including its initial
access write, transaction-cache miss and full pre-state account decoder. -/
theorem body_cost {origin initialized source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {record cutoff ws bs heap pointer : BitVec 64}
    (context : FreshTransaction.Context origin source record bs heap FreshTransaction.tables)
    (records : RunAttempt.InitializedRecords initialized origin cutoff ws bs) (before : cutoff.toNat≤record.toNat)
    (ready : AccountLookup.Environment origin)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word pointer))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤198992 := by
  generalize observed : evaluateHOLFiniteState source body=result
  obtain ⟨outcome,post⟩:=result
  change source.clock-post.clock≤198992
  rcases to_pre_state context addressCell outcome observed with stopped|reached
  · omega
  · obtain ⟨current,inner,last,currentAddress,forward,price,scope,continued,access,state⟩:=reached
    have tail:=after_miss_cost last state records before ready currentAddress
    rw [continued] at tail
    change current.clock-inner.clock≤198961 at tail
    have endpoint:=scope.clock
    omega

theorem call_cost {origin initialized source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {record cutoff ws bs heap : BitVec 64}
    (context : FreshTransaction.Context origin source record bs heap FreshTransaction.tables)
    (records : RunAttempt.InitializedRecords initialized origin cutoff ws bs) (before : cutoff.toNat≤record.toNat)
    (ready : AccountLookup.Environment origin) (pointer : BitVec 64) (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word pointer)]) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "get_account_optional") arguments)).2.clock≤198993 := by
  obtain ⟨callee,called,addressCell⟩:=word_environment source.code.lookup (ofString "get_account_optional") (ofString "addr") body .one pointer
    (original_code source.code context.runtime.code)
  exact ClockCost.call_current source destination (ofString "get_account_optional") arguments _ body callee .one 198992 args called
    (body_cost (context.of_erase rfl) records before ready addressCell)

end InitECandidate.Solver.Input.CurrentVerify.AccountAccess

namespace InitECandidate.Solver.Input.CurrentVerify.AccountRequired
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def body : ProgHOL 64:=match Guest.Software.guestFn_get_account with | .function fn=>progToHOL fn.body | _=>.skip
def afterOptional : ProgHOL 64:=match body with | .decCall _ _ _ _ rest=>rest | _=>.skip

theorem body_shape : body=.decCall (ofString "a") .one (ofString "get_account_optional") [localVar "addr"] afterOptional := by
  simp only [body,afterOptional,Guest.Software.guestFn_get_account,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar]

theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "get_account")=some ([(ofString "addr",.one)],body,.one) := by
  have found:=OriginalCode.indexed code installed 341 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_get_account) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,
    Guest.Software.guestFn_get_account,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using found

/-- The real missing-account branch may create an empty account. Its
complete allocator/store constructor has a static four-tick caller bound. -/
theorem after_optional_price (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code afterOptional 4 := by
  have shape : afterOptional=.seq
      (.ite (.cmp .equal (localVar "a") (.const 1#64))
        (.call (LocalEffects.callInfo (some (some (ofString "a")))) (ofString "acct_empty") []) .skip)
      (.return (localVar "a")) := by
    simp only [afterOptional,body,Guest.Software.guestFn_get_account,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,LocalEffects.callInfo,localVar]
  rw [shape]
  exact ClockCost.sequence code _ _ 4 0
    (ClockCost.conditional code _ _ _ 4 0
      (ClockCost.call_body code (some (some (ofString "a"))) (ofString "acct_empty") [] Mpt.AccountEmpty.formals Mpt.AccountEmpty.body .one 3
        (Mpt.AccountEmpty.original_code code installed) (Mpt.AccountEmpty.body_current_price code installed))
      (ClockCost.skip code))
    (ClockCost.returned code _)

/-- Complete unchanged first required-account lookup, including actual
empty-account construction after the optional sentinel. -/
theorem body_cost {origin initialized source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {record cutoff ws bs heap pointer : BitVec 64}
    (context : FreshTransaction.Context origin source record bs heap FreshTransaction.tables)
    (records : RunAttempt.InitializedRecords initialized origin cutoff ws bs) (before : cutoff.toNat≤record.toNat)
    (ready : AccountLookup.Environment origin)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word pointer))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤198997 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "addr"]=some [.val (.word pointer)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,addressCell]
  obtain ⟨callee,called,cell⟩:=word_environment source.code.lookup (ofString "get_account_optional") (ofString "addr") AccountAccess.body .one pointer
    (AccountAccess.original_code source.code context.runtime.code)
  rw [body_shape]
  exact ClockCost.scoped_current source (ofString "a") .one (ofString "get_account_optional") [localVar "addr"] _ AccountAccess.body afterOptional callee .one
    198992 4 args called (AccountAccess.body_cost (context.of_erase rfl) records before ready cell) (after_optional_price source.code context.runtime.code)

theorem call_cost {origin initialized source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {record cutoff ws bs heap : BitVec 64}
    (context : FreshTransaction.Context origin source record bs heap FreshTransaction.tables)
    (records : RunAttempt.InitializedRecords initialized origin cutoff ws bs) (before : cutoff.toNat≤record.toNat)
    (ready : AccountLookup.Environment origin) (pointer : BitVec 64) (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word pointer)]) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "get_account") arguments)).2.clock≤198998 := by
  obtain ⟨callee,called,addressCell⟩:=word_environment source.code.lookup (ofString "get_account") (ofString "addr") body .one pointer
    (original_code source.code context.runtime.code)
  exact ClockCost.call_current source destination (ofString "get_account") arguments _ body callee .one 198997 args called
    (body_cost (context.of_erase rfl) records before ready addressCell)

end InitECandidate.Solver.Input.CurrentVerify.AccountRequired

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountAccess.after_miss_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountAccess.body_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountAccess.call_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountRequired.body_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountRequired.original_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountRequired.after_optional_price
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountRequired.body_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountRequired.call_cost

namespace InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- A genuine normal provider suffix returns its freshly allocated account,
with the current decoder's actual image and retained earlier memory.
Empty references are current typed globals, not assumed parser outputs. -/
theorem after_alloc_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap out emptyRoot emptyHash : BitVec 64)
    (leafCell : source.locals.lookup (ofString "leaf")=some (Mpt.TrieWalk.triple 1#64 pointer length))
    (outputCell : source.locals.lookup (ofString "a")=some (.val (.word out)))
    (arena : Rlp.LiveArena source) (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤2952790016)
    (before : length≠0#64 → pointer.toNat+length.toNat≤heap.toNat)
    (inputLower : length≠0#64 → 2701131776≤pointer.toNat)
    (sizeBound : 16*length.toNat<2^64)
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)))
    (rootArena : AllocatedBytes.Arena emptyRoot 32) (hashArena : AllocatedBytes.Arena emptyHash 32)
    (output : Mpt.AccountDecode.Output out) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterAlloc=(some (.returned returned),post)) :
    returned=.val (.word out) ∧ Nonempty (Mpt.AccountDecode.Image post out) ∧ Rlp.LiveArena post ∧ heap.toNat+64≤2952790016 ∧
      MemoryMetadata.erase post=MemoryMetadata.erase (PersistentAlloc.post source heap 64#64) ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat → query.toNat<out.toNat ∨ out.toNat+56≤query.toNat → post.memory query=source.memory query) ∧
      source.clock-post.clock≤191*length.toNat+262 := by
  have price:=after_alloc_cost source pointer length heap out leafCell outputCell arena heapCell heapBound before sizeBound output
  rw [normal] at price
  rw [after_alloc_shape] at normal
  have safe : LocalPrefix (ofString "a") decode:=.call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,decodeRun,returnRun,locals⟩:=safe.normal_continue source post (.return (localVar "a")) returned normal
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) decodeArguments=some (Mpt.AccountDecode.values pointer length out):=by
    simp [decodeArguments,Mpt.AccountDecode.values,Mpt.TrieWalk.triple,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,leafCell,outputCell]
  obtain ⟨funded,⟨image⟩,nextArena,room,metadata,window,cost⟩:=Mpt.AccountDecode.Current.ignored_normal source middle pointer length heap out emptyRoot emptyHash
    arena heapCell heapBound before inputLower sizeBound rootGlobal hashGlobal rootArena hashArena output arena.code decodeArguments args decodeRun
  obtain ⟨read,postEq⟩:=return_normal middle post (localVar "a") returned returnRun
  have currentOutput:=locals.trans outputCell
  have expected : eval middle (localVar "a")=some (.val (.word out)):=by simp [eval,evalHOLExact,localVar,toExact,currentOutput]
  have result:=Option.some.inj (read.symm.trans expected)
  refine ⟨result,?_,?_,room,?_,?_,price⟩
  · rw [postEq]
    exact ⟨Mpt.AccountDecode.Image.of_agreement middle _ out image rfl rfl rfl⟩
  · rw [postEq]
    exact nextArena.of_frame rfl
  · rw [postEq]
    exact metadata
  · rw [postEq]
    exact window

end InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional.after_alloc_normal

namespace InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The normal present-account path derives both real allocations from
its actual execution. Their account/record writes protect every word before
the entering heap and preserve the initialized runtime outside heap growth. -/
theorem after_guard_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (ws bs pointer length emptyRoot emptyHash : BitVec 64) (ready : Ready source ws bs)
    (leafCell : source.locals.lookup (ofString "leaf")=some (Mpt.TrieWalk.triple 1#64 pointer length))
    (small : length.toNat≤1024) (property : Mpt.WitnessCore.WitnessValue ws pointer length)
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)))
    (rootArena : AllocatedBytes.Arena emptyRoot 32) (hashArena : AllocatedBytes.Arena emptyHash 32)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterGuard=(some (.returned returned),post)) :
    ∃ out,source.globals.lookup (ofString "heap_ptr")=some (.val (.word out)) ∧ bs.toNat+80≤out.toNat ∧
      returned=.val (.word out) ∧ Nonempty (Mpt.AccountDecode.Image post out) ∧ PersistentNormalFrame source post out := by
  obtain ⟨heap,heapCell,afterBs,bounded,aligned⟩:=ready.heap
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [.const 56#64]=some (PersistentAlloc.values 56#64):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,PersistentAlloc.values]
  rcases CurrentAlloc.scoped_classified source post "a" [.const 56#64] afterAlloc heap 56#64 args ready.environment.keccak.installed heapCell bounded
      (some (.returned returned)) (by rw [←after_guard_shape]; exact normal) with stopped|reached
  · exact (stopped.2 returned rfl).elim
  · obtain ⟨funded,room,inner,continued,endpoint⟩:=reached
    let current:=bind (PersistentAlloc.post {source with clock:=source.clock-1} heap 56#64) "a" heap
    let next:=PersistentAlloc.rounded heap 56#64
    have heapLower : 2701131776≤heap.toNat:=by have lower:=ready.lower; have before:=ready.wsBeforeBs; omega
    have heapArena : AllocatedBytes.Arena heap 0:=⟨heapLower,by omega⟩
    have first : PersistentNormalFrame source current heap:=
      (PersistentAlloc.post_persistent_frame source heap 56#64 heapArena room).of_erase source (PersistentAlloc.post source heap 56#64) source current heap rfl rfl
    have currentStartup:=first.current_arena ready.environment.arena
    have currentLeaf : current.locals.lookup (ofString "leaf")=some (Mpt.TrieWalk.triple 1#64 pointer length):=
      (bind_lookup_other _ "a" "leaf" heap (by decide)).trans leafCell
    have currentOutput : current.locals.lookup (ofString "a")=some (.val (.word heap)):=bind_lookup_same _ _ _
    have currentHeap : current.globals.lookup (ofString "heap_ptr")=some (.val (.word next)):=by
      simp [current,next,PersistentAlloc.post,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
    have guards:=PersistentAlloc.guards heap 56#64 room
    have grows : heap.toNat+56≤next.toNat:=guards.2.2.1
    have output : Mpt.AccountDecode.Output heap:=⟨heapLower,by change heap.toNat+56≤2952790016 at room; omega,aligned⟩
    have before : length≠0#64 → pointer.toNat+length.toNat≤next.toNat:=by
      intro nonempty
      rcases property with empty|bounds
      · exact (nonempty empty).elim
      · have prior:=ready.wsBeforeBs; omega
    have inputLower : length≠0#64 → 2701131776≤pointer.toNat:=by
      intro nonempty
      rcases property with empty|bounds
      · exact (nonempty empty).elim
      · exact bounds.1
    change evaluateHOLFiniteState current afterAlloc=(some (.returned returned),inner) at continued
    obtain ⟨result,⟨image⟩,arena,recordsRoom,metadata,window,price⟩:=after_alloc_normal current inner pointer length next heap emptyRoot emptyHash
      currentLeaf currentOutput (Rlp.LiveArena.of_startup currentStartup) currentHeap guards.2.2.2.1 before inputLower (by omega)
      ((first.globals _ (by decide)).trans rootGlobal) ((first.globals _ (by decide)).trans hashGlobal) rootArena hashArena output returned continued
    have nextArena : AllocatedBytes.Arena next 0:=⟨by omega,by have cap:=guards.2.2.2.1; omega⟩
    have seed:=PersistentAlloc.post_persistent_frame current next 64#64 nextArena recordsRoom
    obtain ⟨last,lastCell,lastArena,lastBound,lastAligned,lastGrows⟩:=seed.nextHeap
    have seedSmall : PersistentNormalFrame current (PersistentAlloc.post current next 64#64) heap:=
      ⟨⟨last,lastCell,lastArena,lastBound,lastAligned,by omega⟩,seed.metadata,seed.globals,
        fun query earlier=>seed.memory query (by omega)⟩
    have second:=PersistentNormalFrame.after_memory current (PersistentAlloc.post current next 64#64) inner heap seedSmall metadata (by
      intro query earlier
      exact window query (by omega) (Or.inl earlier))
    have total:=PersistentNormalFrame.trans source current inner heap heap first second (Nat.le_refl _)
    refine ⟨heap,heapCell,afterBs,result,?_,?_⟩
    · rw [endpoint]
      exact ⟨Mpt.AccountDecode.Image.of_agreement inner _ heap image rfl rfl rfl⟩
    · apply total.of_erase source inner source post heap rfl
      rw [endpoint]
      rfl

end InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional.after_guard_normal

namespace InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The actual leaf guard classifies every normal suffix: absence returns
sentinel1 without changing the nonlocal state; presence produces the real
account with both allocation and earlier-memory guarantees. -/
theorem after_leaf_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (ws bs emptyRoot emptyHash : BitVec 64) (ready : Ready source ws bs)
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)))
    (rootArena : AllocatedBytes.Arena emptyRoot 32) (hashArena : AllocatedBytes.Arena emptyHash 32)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterLeaf=(some (.returned returned),post)) :
    (returned=.val (.word 1#64) ∧ LocalEffects.erase post=LocalEffects.erase source) ∨
      ∃ out,source.globals.lookup (ofString "heap_ptr")=some (.val (.word out)) ∧ bs.toNat+80≤out.toNat ∧
        returned=.val (.word out) ∧ Nonempty (Mpt.AccountDecode.Image post out) ∧ PersistentNormalFrame source post out := by
  obtain ⟨answer,leafCell,result⟩:=ready.leaf
  rcases result with absent|present
  · rw [absent] at leafCell
    have actual:=absent_after_leaf source leafCell
    rw [actual] at normal
    have resultEq:=congrArg Prod.fst normal
    have postEq:=congrArg Prod.snd normal
    change emptyLocalsHOLFinite source=post at postEq
    have valueEq : returned=.val (.word 1#64):=by
      simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using resultEq.symm
    exact Or.inl ⟨valueEq,by rw [←postEq]; rfl⟩
  · obtain ⟨pointer,length,valueEq,payload,property⟩:=present
    rw [valueEq] at leafCell
    rw [present_after_leaf source pointer length leafCell] at normal
    exact Or.inr (after_guard_normal source post ws bs pointer length emptyRoot emptyHash ready leafCell payload.1 property
      rootGlobal hashGlobal rootArena hashArena returned normal)

end InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional.after_leaf_normal

namespace InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The real release followed by return changes only the heap global and
clock before clearing lexical locals. Its saved mark is a current input. -/
theorem finish_normal_state (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (mark old : BitVec 64)
    (markCell : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word old)))
    (installed : OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source finish=(some (.returned returned),post)) :
    post=emptyLocalsHOLFinite (HeapScope.releasePost {source with clock:=source.clock-1} mark) := by
  have safe : LocalPrefix (ofString "r") (.call (some (none,none)) (ofString "heap_release") [localVar "mark"]):=
    .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,released,tailRun,locals⟩:=safe.normal_continue source post (.return (localVar "r")) returned normal
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "mark"]=some [.val (.word mark)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,markCell]
  have releaseEq:=HeapScope.release_normal source middle mark old [localVar "mark"] args heap installed released
  have postEq:=(return_normal middle post (localVar "r") returned tailRun).2
  rw [postEq,releaseEq]

/-- The actual initialized lookup and release restore their saved heap
mark and preserve every word beyond the low hash/nibble workspace. -/
theorem lookup_normal_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ws bs out mark old : BitVec 64)
    (entry : Entry source ws bs) (arena : AllocatedBytes.Arena out 32) (fresh : bs.toNat≤out.toNat)
    (outCell : source.locals.lookup (ofString "h")=some (.val (.word out)))
    (markCell : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word old)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source lookup=(some (.returned returned),post)) :
    MemoryMetadata.erase post=MemoryMetadata.erase (HeapScope.releasePost source mark) ∧
      ∀ query : BitVec 64,2701135464≤query.toNat → post.memory query=source.memory query := by
  obtain ⟨db,target,answer,inner,dbBefore,result,frame,finishRun,restored⟩:=lookup_normal_trace source post ws bs out entry arena fresh outCell returned normal
  let ready:=CallNormal.continuationEntry source target "r" answer
  have readyMark : ready.locals.lookup (ofString "mark")=some (.val (.word mark)):=
    (CallNormal.continuation_lookup_other source target "r" "mark" answer (by decide)).trans markCell
  have metadata : MemoryMetadata.erase target=MemoryMetadata.erase source:=frame.fields
  have globals:=congrArg PanSemStateFiniteExact.globals metadata
  change target.globals=source.globals at globals
  have readyHeap : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word old)):=by
    change target.globals.lookup (ofString "heap_ptr")=some (.val (.word old))
    rw [globals]; exact heap
  have readyInstalled : OriginalCode.Installed ready.code:=by
    change OriginalCode.Installed target.code
    rw [MemoryMetadata.code metadata]
    exact entry.environment.keccak.installed
  have actual:=finish_normal_state ready inner mark old readyMark readyHeap readyInstalled returned finishRun
  constructor
  · rw [restored,actual]
    have inherited:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>HeapScope.releasePost state mark) metadata
    exact inherited
  · intro query lower
    rw [restored,actual]
    exact frame.memory query (by
      intro offset inside
      exact (CopyGeneral.Away.before 2701134704#64 query 64 2701134768 (by decide) (by decide) (by omega) offset inside).2)

end InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf.lookup_normal_trace
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf.finish_normal_state
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf.lookup_normal_frame

namespace InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The actual software hash and lookup/release suffix retain runtime
metadata with the saved heap mark restored. Earlier input/table words are
protected; only the low workspace and fresh digest can be written. -/
theorem after_alloc_normal_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (ws bs address out mark old : BitVec 64)
    (entry : Entry source ws bs) (arena : AllocatedBytes.Arena out 32) (aligned : out.toNat%8=0) (fresh : bs.toNat≤out.toNat)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word address)))
    (outCell : source.locals.lookup (ofString "h")=some (.val (.word out)))
    (markCell : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word old)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterAlloc=(some (.returned returned),post)) :
    MemoryMetadata.erase post=MemoryMetadata.erase (HeapScope.releasePost source mark) ∧
      ∀ query : BitVec 64,2701135464≤query.toNat → query.toNat<out.toNat → post.memory query=source.memory query := by
  have safe : LocalPrefix (ofString "h") hash:=.call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,hashRun,lookupRun,outEq⟩:=safe.normal_continue source post lookup returned normal
  have args:=hash_arguments source address out addressCell outCell
  have next:=hash_after entry arena aligned fresh args hashRun
  have hashMetadata:=CurrentKeccak.Hash.call_metadata source.code entry.environment.keccak.installed hashArguments (some none) source rfl
  change MemoryMetadata.erase (evaluateHOLFiniteState source hash).2=MemoryMetadata.erase source at hashMetadata
  rw [hashRun] at hashMetadata
  have globals:=congrArg PanSemStateFiniteExact.globals hashMetadata
  change middle.globals=source.globals at globals
  have middleMark : middle.locals.lookup (ofString "mark")=some (.val (.word mark)):=
    (CallNormal.ignored_lookup source middle (ofString "mark") (ofString "keccak256") hashArguments hashRun).trans markCell
  have middleHeap : middle.globals.lookup (ofString "heap_ptr")=some (.val (.word old)):=by rw [globals]; exact heap
  obtain ⟨lookupMetadata,lookupMemory⟩:=lookup_normal_frame middle post ws bs out mark old next arena fresh (outEq.trans outCell) middleMark middleHeap returned lookupRun
  constructor
  · have inherited:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>HeapScope.releasePost state mark) hashMetadata
    exact lookupMetadata.trans inherited
  · intro query lower earlier
    have stateAway:=CopyGeneral.Away.before 2701132160#64 query 200 2701132360 (by decide) (by decide) (by omega)
    have padAway:=CopyGeneral.Away.before 2701132360#64 query 136 2701132496 (by decide) (by decide) (by omega)
    have outAway:=CopyGeneral.Away.after out query 32 aligned (by have bound:=arena.upper; omega) earlier
    have hashMemory:=(CurrentKeccak.Hash.call_span_frame source middle 2701132160#64 2701132360#64 address out query 20
      entry.environment.keccak hashArguments args (by decide) arena stateAway padAway outAway hashRun).memory
    exact (lookupMemory query lower).trans hashMemory

private theorem heap_update_shadow (globals : HolFiniteMapExact MlS (ValueHOL 64)) (old next : BitVec 64) :
    (globals.update (ofString "heap_ptr",.val (.word old))).update (ofString "heap_ptr",.val (.word next))=globals.update (ofString "heap_ptr",.val (.word next)) := by
  apply HolFiniteMapExact.ext
  funext key
  simp only [HolFiniteMapExact.lookup_update_pointwise]
  by_cases same : key=ofString "heap_ptr" <;> simp [same]

/-- The temporary allocation's heap update is discarded by the genuine
later release, while memory/clock/local fields are erased for metadata. -/
theorem allocated_release_metadata (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap mark : BitVec 64) :
    MemoryMetadata.erase (HeapScope.releasePost (bind (PersistentAlloc.post {source with clock:=source.clock-1} heap 32#64) "h" heap) mark)=
      MemoryMetadata.erase (HeapScope.releasePost source mark) := by
  simp only [MemoryMetadata.erase,HeapScope.releasePost,PersistentAlloc.post,QueryBranch.bind,setVarHOLFinite,emptyLocalsHOLFinite]
  rw [heap_update_shadow]

/-- Actual allocation room is derived from the normal caller. The full
hash/trie/release continuation then protects the original earlier interval. -/
theorem after_mark_normal_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (ws bs address mark heap : BitVec 64)
    (entry : Entry source ws bs)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word address)))
    (markCell : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (bounded : heap.toNat≤2952790016) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterMark=(some (.returned returned),post)) :
    MemoryMetadata.erase post=MemoryMetadata.erase (HeapScope.releasePost source mark) ∧
      ∀ query : BitVec 64,2701135464≤query.toNat → query.toNat<heap.toNat → post.memory query=source.memory query := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [.const 32#64]=some (PersistentAlloc.values 32#64):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,PersistentAlloc.values]
  rcases CurrentAlloc.scoped_classified source post "h" [.const 32#64] afterAlloc heap 32#64 args entry.environment.keccak.installed heapCell bounded _ normal with stopped|reached
  · exact (stopped.2 returned rfl).elim
  · obtain ⟨funded,room,inner,continued,endpoint⟩:=reached
    let ready:=bind (PersistentAlloc.post {source with clock:=source.clock-1} heap 32#64) "h" heap
    obtain ⟨next,arena,aligned,fresh⟩:=allocated_entry source ws bs heap entry heapCell room
    have currentAddress : ready.locals.lookup (ofString "addr")=some (.val (.word address)):=
      (bind_lookup_other _ "h" "addr" heap (by decide)).trans addressCell
    have currentMark : ready.locals.lookup (ofString "mark")=some (.val (.word mark)):=
      (bind_lookup_other _ "h" "mark" heap (by decide)).trans markCell
    have currentHeap : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 32#64))):=by
      simp [ready,PersistentAlloc.post,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
    obtain ⟨metadata,memory⟩:=after_alloc_normal_frame ready inner ws bs address heap mark (PersistentAlloc.rounded heap 32#64) next arena aligned fresh
      currentAddress (bind_lookup_same _ _ _) currentMark currentHeap returned continued
    constructor
    · rw [endpoint]
      exact metadata.trans (allocated_release_metadata source heap mark)
    · intro query lower earlier
      rw [endpoint]
      exact memory query lower earlier

/-- Complete unchanged ws_account_leaf normal memory/runtime contract.
The saved mark and actual temporary allocation come from this execution;
real hash/nibble workspace writes are excluded from the retained interval. -/
theorem body_normal_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (ws bs address heap : BitVec 64) (entry : Entry source ws bs)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word address)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (bounded : heap.toNat≤2952790016) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    MemoryMetadata.erase post=MemoryMetadata.erase source ∧
      ∀ query : BitVec 64,2701135464≤query.toNat → query.toNat<heap.toNat → post.memory query=source.memory query := by
  rw [body_shape] at normal
  have installed:=entry.environment.keccak.installed
  have funded:=CallNormal.normal_clock source post (ofString "mark") .one (ofString "heap_mark") [] afterMark returned normal
  let ready:=bind {source with clock:=source.clock-1} "mark" heap
  let inner:=(evaluateHOLFiniteState ready afterMark).2
  have actual:=HeapScope.mark_call_execute source heap "mark" afterMark heapCell (HeapScope.mark_original_code source.code installed) funded
  have joined:=actual.symm.trans normal
  have resultEq:=congrArg Prod.fst joined
  change (evaluateHOLFiniteState ready afterMark).1=some (.returned returned) at resultEq
  have innerRun : evaluateHOLFiniteState ready afterMark=(some (.returned returned),inner):=Prod.ext resultEq rfl
  have postEq:=(congrArg Prod.snd joined).symm
  change post=restore source "mark" inner at postEq
  have currentAddress : ready.locals.lookup (ofString "addr")=some (.val (.word address)):=
    (bind_lookup_other _ "mark" "addr" heap (by decide)).trans addressCell
  obtain ⟨metadata,memory⟩:=after_mark_normal_frame ready inner ws bs address heap heap (entry.of_frame rfl)
    currentAddress (bind_lookup_same _ _ _) heapCell bounded returned innerRun
  have unchanged : source.globals.update (ofString "heap_ptr",.val (.word heap))=source.globals:=by
    apply HolFiniteMapExact.ext
    funext key
    simp only [HolFiniteMapExact.lookup_update_pointwise]
    by_cases same : key=ofString "heap_ptr"
    · subst key; simp [heapCell]
    · simp [same]
  constructor
  · rw [postEq]
    have released : MemoryMetadata.erase (HeapScope.releasePost ready heap)=MemoryMetadata.erase source:=by
      change MemoryMetadata.erase {source with globals:=source.globals.update (ofString "heap_ptr",.val (.word heap))}=
        MemoryMetadata.erase source
      rw [unchanged]
    exact metadata.trans released
  · intro query lower earlier
    rw [postEq]
    exact memory query lower earlier

end InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf.after_alloc_normal_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf.allocated_release_metadata
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf.after_mark_normal_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf.body_normal_frame

namespace InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- A genuine normal leaf caller exposes the actual bounded witness
answer and retained runtime/earlier-memory frame to its real continuation. -/
theorem scoped_normal_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (ws bs address heap : BitVec 64) (entry : Entry source ws bs)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (bounded : heap.toNat≤2952790016) (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word address)])
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) Mpt.TrieWalk.resultShape (ofString "ws_account_leaf") arguments continuation)=(some (.returned returned),post)) :
    ∃ target answer inner db,db.toNat≤ws.toNat ∧
      Mpt.TrieWalk.Answer target.memaddrs 1024 (property:=Mpt.WitnessCore.WitnessValue db) answer ∧
      MemoryMetadata.erase target=MemoryMetadata.erase source ∧
      (∀ query : BitVec 64,2701135464≤query.toNat → query.toNat<heap.toNat → target.memory query=source.memory query) ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source target name answer) continuation=(some (.returned returned),inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called,addressCell⟩:=word_environment source.code.lookup (ofString "ws_account_leaf") (ofString "addr") body Mpt.TrieWalk.resultShape address
    (original_code source.code entry.environment.keccak.installed)
  obtain ⟨funded,target,answer,inner,bodyRun,checked,continued,endpoint⟩:=
    CallNormal.scoped_normal source post name Mpt.TrieWalk.resultShape (ofString "ws_account_leaf") arguments _ body continuation callee Mpt.TrieWalk.resultShape args called returned normal
  let current:=callEntryStateHOLFinite source callee
  have currentEntry : Entry current ws bs:=entry.of_frame rfl
  obtain ⟨db,dbBefore,actualAnswer⟩:=body_normal_value current target ws bs address currentEntry addressCell answer bodyRun
  obtain ⟨metadata,memory⟩:=body_normal_frame current target ws bs address heap currentEntry addressCell heapCell bounded answer bodyRun
  exact ⟨target,answer,inner,db,dbBefore,actualAnswer,metadata,memory,continued,endpoint⟩

end InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Leaf.scoped_normal_frame

namespace InitECandidate.Solver.Input.CurrentVerify.AccountLookup
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- A normal account provider advances its actual bounded heap and retains
nonheap runtime fields and earlier input/table memory. Low workspace writes
remain allowed, unlike a full persistent-allocation frame. -/
structure Frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) : Prop where
  nextHeap : NormalHeapEffects.AtLeast heap.toNat target
  metadata : MemoryMetadata.erase {target with globals:=source.globals}=MemoryMetadata.erase source
  globals : HeapGlobals source target
  memory : ∀ query : BitVec 64,2701135464≤query.toNat → query.toNat<heap.toNat → target.memory query=source.memory query

end InitECandidate.Solver.Input.CurrentVerify.AccountLookup

namespace InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The complete unchanged optional provider returns sentinel1 or its real
physical account and protects earlier initialized state through the actual
leaf hash/lookup, restored temporary heap and decoder allocations. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (ws bs address emptyRoot emptyHash : BitVec 64) (entry : Entry source ws bs)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word address)))
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)))
    (rootArena : AllocatedBytes.Arena emptyRoot 32) (hashArena : AllocatedBytes.Arena emptyHash 32)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    ∃ heap,source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧ bs.toNat+80≤heap.toNat ∧ Frame source post heap ∧
      (returned=.val (.word 1#64) ∨ ∃ out,bs.toNat+80≤out.toNat ∧ returned=.val (.word out) ∧ Nonempty (Mpt.AccountDecode.Image post out)) := by
  obtain ⟨heap,heapCell,afterBs,bounded,aligned⟩:=entry.heap
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "addr"]=some [.val (.word address)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,addressCell]
  rw [body_shape] at normal
  obtain ⟨target,answer,inner,db,dbBefore,actualAnswer,metadata,memory,continued,endpoint⟩:=Leaf.scoped_normal_frame source post ws bs address heap entry
    heapCell bounded "leaf" [localVar "addr"] afterLeaf args returned normal
  let current:=CallNormal.continuationEntry source target "leaf" answer
  have targetEnvironment:=entry.environment.of_metadata metadata
  have globals:=congrArg PanSemStateFiniteExact.globals metadata
  change target.globals=source.globals at globals
  have currentHeap : current.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by
    change target.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
    rw [globals]; exact heapCell
  have boundedAnswer : Mpt.TrieWalk.Answer current.memaddrs 1024 (property:=Mpt.WitnessCore.WitnessValue ws) answer:=by
    rcases actualAnswer with absent|present
    · exact Or.inl absent
    · obtain ⟨pointer,length,equal,payload,property⟩:=present
      refine Or.inr ⟨pointer,length,equal,payload,?_⟩
      rcases property with empty|bounds
      · exact Or.inl empty
      · exact Or.inr ⟨bounds.1,Nat.le_trans bounds.2 dbBefore⟩
  have ready : Ready current ws bs:=⟨targetEnvironment.of_metadata rfl,⟨heap,currentHeap,afterBs,bounded,aligned⟩,entry.wsBeforeBs,entry.lower,
    answer,CallNormal.continuation_lookup_same source target "leaf" answer,boundedAnswer⟩
  have currentRoot : current.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)):=by
    change target.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot))
    rw [globals]; exact rootGlobal
  have currentHash : current.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)):=by
    change target.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash))
    rw [globals]; exact hashGlobal
  rcases after_leaf_normal current inner ws bs emptyRoot emptyHash ready currentRoot currentHash rootArena hashArena returned continued with absent|present
  · obtain ⟨result,pure⟩:=absent
    have fullMetadata : MemoryMetadata.erase post=MemoryMetadata.erase source:=by
      rw [endpoint]
      exact (MemoryMetadata.of_frame pure).trans metadata
    have reset:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>MemoryMetadata.erase {state with globals:=source.globals}) fullMetadata
    change MemoryMetadata.erase {post with globals:=source.globals}=MemoryMetadata.erase source at reset
    have finalGlobals:=congrArg PanSemStateFiniteExact.globals fullMetadata
    change post.globals=source.globals at finalGlobals
    have finalHeap : post.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by rw [finalGlobals]; exact heapCell
    refine ⟨heap,heapCell,afterBs,⟨⟨heap,finalHeap,Nat.le_refl _,bounded,aligned⟩,reset,?_,?_⟩,Or.inl result⟩
    · intro key other
      rw [finalGlobals]
    · intro query lower earlier
      have suffixMemory:=LocalEffects.memory_of_erase current inner pure
      rw [endpoint]
      exact (congrFun suffixMemory query).trans (memory query lower earlier)
  · obtain ⟨out,outCell,outAfter,result,⟨image⟩,suffix⟩:=present
    have same : out=heap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (outCell.symm.trans currentHeap)))
    subst out
    obtain ⟨last,lastCell,lastArena,lastBound,lastAligned,grows⟩:=suffix.nextHeap
    have fullMetadata:=suffix.metadata.trans metadata
    have runtime : MemoryMetadata.erase {post with globals:=source.globals}=MemoryMetadata.erase source:=by
      rw [endpoint]
      change MemoryMetadata.erase {inner with globals:=source.globals}=MemoryMetadata.erase source
      have prefixGlobals : current.globals=source.globals:=globals
      rw [prefixGlobals] at fullMetadata
      exact fullMetadata
    have finalHeap : post.globals.lookup (ofString "heap_ptr")=some (.val (.word last)):=by rw [endpoint]; exact lastCell
    refine ⟨heap,heapCell,afterBs,⟨⟨last,finalHeap,grows,lastBound,lastAligned⟩,runtime,?_,?_⟩,
      Or.inr ⟨heap,outAfter,result,?_⟩⟩
    · intro key other
      rw [endpoint]
      exact (suffix.globals key other).trans (congrArg (fun fields=>fields.lookup key) globals)
    · intro query lower earlier
      rw [endpoint]
      exact (suffix.memory query earlier).trans (memory query lower earlier)
    · rw [endpoint]
      exact ⟨Mpt.AccountDecode.Image.of_agreement inner _ heap image rfl rfl rfl⟩

end InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional.body_normal

namespace InitECandidate.Solver.Input.CurrentVerify.AccountLookup
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Actual callee entry and caller local restoration retain the same
bounded heap and earlier input/table interval. -/
theorem Frame.of_erase (source target source' target' : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (frame : Frame source target heap)
    (entry : LocalEffects.erase source'=LocalEffects.erase source)
    (exit : LocalEffects.erase target'=LocalEffects.erase target) : Frame source' target' heap := by
  have sourceGlobals:=congrArg PanSemStateFiniteExact.globals entry
  have targetGlobals:=congrArg PanSemStateFiniteExact.globals exit
  change source'.globals=source.globals at sourceGlobals
  change target'.globals=target.globals at targetGlobals
  have sourceMemory:=LocalEffects.memory_of_erase source source' entry
  have targetMemory:=LocalEffects.memory_of_erase target target' exit
  have metadata:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with globals:=source.globals}) (MemoryMetadata.of_frame exit)
  change MemoryMetadata.erase {target' with globals:=source.globals}=MemoryMetadata.erase {target with globals:=source.globals} at metadata
  have total:=metadata.trans (frame.metadata.trans (MemoryMetadata.of_frame entry).symm)
  rw [←sourceGlobals] at total
  obtain ⟨next,cell,grows,bounded,aligned⟩:=frame.nextHeap
  refine ⟨⟨next,by rw [targetGlobals]; exact cell,grows,bounded,aligned⟩,total,?_,?_⟩
  · intro key other
    rw [targetGlobals,sourceGlobals]
    exact frame.globals key other
  · intro query lower earlier
    rw [targetMemory,sourceMemory]
    exact frame.memory query lower earlier

end InitECandidate.Solver.Input.CurrentVerify.AccountLookup

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Frame.of_erase

namespace InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- A real scoped optional-provider caller derives its actual return,
heap interval and account image before exposing its real continuation. -/
theorem scoped_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (ws bs address emptyRoot emptyHash : BitVec 64) (entry : Entry source ws bs)
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)))
    (rootArena : AllocatedBytes.Arena emptyRoot 32) (hashArena : AllocatedBytes.Arena emptyHash 32)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word address)])
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "ws_get_account_optional") arguments continuation)=(some (.returned returned),post)) :
    ∃ target answer inner heap,source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧ bs.toNat+80≤heap.toNat ∧
      Frame source target heap ∧
      (answer=.val (.word 1#64) ∨ ∃ out,bs.toNat+80≤out.toNat ∧ answer=.val (.word out) ∧ Nonempty (Mpt.AccountDecode.Image target out)) ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source target name answer) continuation=(some (.returned returned),inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called,addressCell⟩:=word_environment source.code.lookup (ofString "ws_get_account_optional") (ofString "addr") body .one address
    (original_code source.code entry.environment.keccak.installed)
  obtain ⟨funded,target,answer,inner,bodyRun,checked,continued,endpoint⟩:=
    CallNormal.scoped_normal source post name .one (ofString "ws_get_account_optional") arguments _ body continuation callee .one args called returned normal
  let current:=callEntryStateHOLFinite source callee
  obtain ⟨heap,heapCell,afterBs,frame,result⟩:=body_normal current target ws bs address emptyRoot emptyHash (entry.of_frame rfl) addressCell
    rootGlobal hashGlobal rootArena hashArena answer bodyRun
  exact ⟨target,answer,inner,heap,heapCell,afterBs,frame.of_erase current target source target heap rfl rfl,result,continued,endpoint⟩

end InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Optional.scoped_normal

namespace InitECandidate.Solver.Input.CurrentVerify.PreStateAccount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The actual recorded-read continuation now retains its complete provider
normal image/frame through the real caller and literal final return. -/
theorem after_record_normal {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {cutoff ws bs table record heap : BitVec 64}
    (state : RecordPreStateRead.Recorded origin source cutoff ws bs table record heap)
    (ready : AccountLookup.Environment source) (address : BitVec 64)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word address)))
    (emptyRoot emptyHash : BitVec 64)
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)))
    (rootArena : AllocatedBytes.Arena emptyRoot 32) (hashArena : AllocatedBytes.Arena emptyHash 32)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterRecord=(some (.returned returned),post)) :
    ∃ start,source.globals.lookup (ofString "heap_ptr")=some (.val (.word start)) ∧ bs.toNat+80≤start.toNat ∧ AccountLookup.Frame source post start ∧
      (returned=.val (.word 1#64) ∨ ∃ out,bs.toNat+80≤out.toNat ∧ returned=.val (.word out) ∧ Nonempty (Mpt.AccountDecode.Image post out)) := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "addr"]=some [.val (.word address)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,addressCell]
  rw [after_record_shape] at normal
  obtain ⟨target,answer,inner,start,heapCell,afterBs,frame,result,continued,endpoint⟩:=AccountLookup.Optional.scoped_normal source post ws bs address emptyRoot emptyHash
    (AccountLookup.Entry.of_recorded state ready) rootGlobal hashGlobal rootArena hashArena "a" [localVar "addr"] (.return (localVar "a")) args returned normal
  let current:=CallNormal.continuationEntry source target "a" answer
  have cell : current.locals.lookup (ofString "a")=some answer:=CallNormal.continuation_lookup_same _ _ _ _
  have expected : eval current (localVar "a")=some answer:=by simp [eval,evalHOLExact,localVar,toExact,cell]
  obtain ⟨read,postEq⟩:=return_normal current inner (localVar "a") returned continued
  have same : returned=answer:=Option.some.inj (read.symm.trans expected)
  have actual : LocalEffects.erase post=LocalEffects.erase target:=by rw [endpoint,postEq]; rfl
  refine ⟨start,heapCell,afterBs,frame.of_erase source target source post start rfl actual,?_⟩
  rcases result with absent|present
  · exact Or.inl (same.trans absent)
  · obtain ⟨out,outAfter,answerEq,⟨image⟩⟩:=present
    have domain:=congrArg PanSemStateFiniteExact.memaddrs actual
    have memory:=LocalEffects.memory_of_erase target post actual
    refine Or.inr ⟨out,outAfter,same.trans answerEq,?_⟩
    exact ⟨Mpt.AccountDecode.Image.of_agreement target post out image domain (congrFun memory _) (congrFun memory _)⟩

end InitECandidate.Solver.Input.CurrentVerify.PreStateAccount

#print axioms InitECandidate.Solver.Input.CurrentVerify.PreStateAccount.after_record_normal

namespace InitECandidate.Solver.Input.CurrentVerify.AccountLookup
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Actual initialized empty-reference cells. Physical32byte arenas for
these fixed pointers follow from their concrete ordinary-memory bounds. -/
structure References (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  root : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word 2701134640#64))
  hash : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word 2701134672#64))

theorem References.of_metadata {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (refs : References source) (metadata : MemoryMetadata.erase target=MemoryMetadata.erase source) : References target := by
  have globals:=congrArg PanSemStateFiniteExact.globals metadata
  change target.globals=source.globals at globals
  exact ⟨by rw [globals]; exact refs.root,by rw [globals]; exact refs.hash⟩

theorem Frame.references {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {heap : BitVec 64}
    (frame : Frame source target heap) (refs : References source) : References target:=
  ⟨(frame.globals _ (by decide)).trans refs.root,(frame.globals _ (by decide)).trans refs.hash⟩

/-- Heap growth and real memory writes preserve the original hash/scratch
workspace cells, domain, endian and installed code under the actual frame. -/
theorem Frame.environment {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {heap : BitVec 64}
    (frame : Frame source target heap) (ready : Environment source) : Environment target := by
  have code:=MemoryMetadata.code frame.metadata
  have domain:=MemoryMetadata.domain frame.metadata
  have endian:=MemoryMetadata.endian frame.metadata
  change target.code=source.code at code
  change target.memaddrs=source.memaddrs at domain
  change target.be=source.be at endian
  exact ⟨⟨by rw [code]; exact ready.keccak.installed,domain.trans ready.keccak.domain,
    (frame.globals _ (by decide)).trans ready.keccak.stateGlobal,(frame.globals _ (by decide)).trans ready.keccak.padGlobal,
    ready.keccak.stateArena,ready.keccak.padArena,ready.keccak.stateAligned,ready.keccak.padAligned⟩,
    endian.trans ready.little,(frame.globals _ (by decide)).trans ready.nibbles,
    ⟨(frame.globals _ (by decide)).trans ready.arena.scratch,(frame.globals _ (by decide)).trans ready.arena.frame,
      domain.trans ready.arena.domain,by rw [code]; exact ready.arena.code⟩⟩

/-- A real returned account retains the actual read-recording entry and
its interval frame, rather than asserting the obsolete full memory snapshot. -/
structure NormalResult (initialized post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (cutoff ws bs record heap : BitVec 64) (returned : ValueHOL 64) : Prop where
  references : References post
  environment : Environment post
  recorded : ∃ current table start,RecordPreStateRead.Recorded initialized current cutoff ws bs table record heap ∧
    current.globals.lookup (ofString "heap_ptr")=some (.val (.word start)) ∧ bs.toNat+80≤start.toNat ∧ Frame current post start
  value : returned=.val (.word 1#64) ∨ ∃ out,bs.toNat+80≤out.toNat ∧ returned=.val (.word out) ∧ Nonempty (Mpt.AccountDecode.Image post out)

/-- Caller-local restoration preserves the real recorded entry, current
account image and actual normal heap/memory frame. -/
theorem NormalResult.of_erase {initialized source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {cutoff ws bs record heap : BitVec 64} {returned : ValueHOL 64}
    (result : NormalResult initialized source cutoff ws bs record heap returned)
    (physical : LocalEffects.erase target=LocalEffects.erase source) : NormalResult initialized target cutoff ws bs record heap returned := by
  have metadata:=MemoryMetadata.of_frame physical
  obtain ⟨current,table,start,state,cell,afterBs,frame⟩:=result.recorded
  refine ⟨result.references.of_metadata metadata,result.environment.of_metadata metadata,
    ⟨current,table,start,state,cell,afterBs,frame.of_erase current source current target start rfl physical⟩,?_⟩
  rcases result.value with absent|present
  · exact Or.inl absent
  · obtain ⟨out,afterBs,returnedEq,⟨image⟩⟩:=present
    have memory:=LocalEffects.memory_of_erase source target physical
    exact Or.inr ⟨out,afterBs,returnedEq,⟨Mpt.AccountDecode.Image.of_agreement source target out image (MemoryMetadata.domain metadata) (congrFun memory _) (congrFun memory _)⟩⟩

end InitECandidate.Solver.Input.CurrentVerify.AccountLookup

namespace InitECandidate.Solver.Input.CurrentVerify.FreshTransaction
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem Context.account_references {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {record bs heap : BitVec 64} {done : List TableSpec}
    (context : Context origin source record bs heap done) (refs : AccountLookup.References origin) : AccountLookup.References source:=
  ⟨(context.globals _ (by decide) (by decide) (by decide)).trans refs.root,
    (context.globals _ (by decide) (by decide) (by decide)).trans refs.hash⟩

end InitECandidate.Solver.Input.CurrentVerify.FreshTransaction

namespace InitECandidate.Solver.Input.CurrentVerify.PreStateAccount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Both the actual initial workspace and empty-reference globals reach
the genuine recorded-read continuation; no future provider state is assumed. -/
theorem to_after_record_references {origin initialized source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {record cutoff ws bs heap access pointer : BitVec 64}
    (context : FreshTransaction.Context origin source record bs heap FreshTransaction.remainingTables)
    (state : AccountAccess.AccessState source record access)
    (records : RunAttempt.InitializedRecords initialized origin cutoff ws bs) (before : cutoff.toNat≤record.toNat)
    (ready : AccountLookup.Environment origin) (refs : AccountLookup.References origin)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word pointer)))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    (source.clock-post.clock≤327 ∧ ∀ value,outcome≠some (.returned value)) ∨
      ∃ current inner table,RecordPreStateRead.Recorded initialized current cutoff ws bs table record heap ∧
        AccountLookup.Environment current ∧ AccountLookup.References current ∧ current.locals.lookup (ofString "addr")=some (.val (.word pointer)) ∧
        CallPrefix.ScopeFrame post inner ∧ evaluateHOLFiniteState current afterRecord=(outcome,inner) := by
  rcases to_after_cache context state records before addressCell outcome run with stopped|reached
  · exact Or.inl ⟨by omega,stopped.2⟩
  · obtain ⟨entered,target,retained,currentRecords,currentAddress,forward,price,scope,continued⟩:=reached
    have currentReady:=retained.account_lookup_environment ready
    have currentRefs:=retained.account_references refs
    rcases miss_record_trace_complete retained currentRecords before currentAddress outcome continued with stopped|reached
    · exact Or.inl ⟨by have clock:=scope.clock; omega,stopped.2⟩
    · obtain ⟨current,inner,table,last,lastAddress,nextForward,nextPrice,nextScope,rest,metadata⟩:=reached
      exact Or.inr ⟨current,inner,table,last,currentReady.of_metadata metadata,currentRefs.of_metadata metadata,lastAddress,scope.trans nextScope,rest⟩

/-- Complete normal first pre-state getter: its actual repeated access,
block-cache miss and recording prefix supply the real provider entry.
The returned physical account and recorded table state survive its scopes. -/
theorem body_normal {origin initialized source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {record cutoff ws bs heap access pointer : BitVec 64}
    (context : FreshTransaction.Context origin source record bs heap FreshTransaction.remainingTables)
    (state : AccountAccess.AccessState source record access)
    (records : RunAttempt.InitializedRecords initialized origin cutoff ws bs) (before : cutoff.toNat≤record.toNat)
    (ready : AccountLookup.Environment origin) (refs : AccountLookup.References origin)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word pointer)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    AccountLookup.NormalResult initialized post cutoff ws bs record heap returned := by
  rcases to_after_record_references context state records before ready refs addressCell _ normal with stopped|reached
  · exact (stopped.2 returned rfl).elim
  · obtain ⟨current,inner,table,last,currentReady,currentRefs,currentAddress,scope,continued⟩:=reached
    obtain ⟨start,cell,afterBs,frame,result⟩:=after_record_normal last currentReady pointer currentAddress 2701134640#64 2701134672#64
      currentRefs.root currentRefs.hash ⟨by decide,by decide⟩ ⟨by decide,by decide⟩ returned continued
    have actual : AccountLookup.NormalResult initialized inner cutoff ws bs record heap returned:=
      ⟨frame.references currentRefs,frame.environment currentReady,⟨current,table,start,last,cell,afterBs,frame⟩,result⟩
    exact actual.of_erase scope.metadata

end InitECandidate.Solver.Input.CurrentVerify.PreStateAccount

#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.References.of_metadata
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Frame.references
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.Frame.environment
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountLookup.NormalResult.of_erase
#print axioms InitECandidate.Solver.Input.CurrentVerify.FreshTransaction.Context.account_references
#print axioms InitECandidate.Solver.Input.CurrentVerify.PreStateAccount.to_after_record_references
#print axioms InitECandidate.Solver.Input.CurrentVerify.PreStateAccount.body_normal

namespace InitECandidate.Solver.Input.CurrentVerify.PreStateAccount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The actual scoped pre-state caller supplies its normal account result
and real recorded-state frame before exposing the genuine continuation. -/
theorem scoped_normal {origin initialized source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {record cutoff ws bs heap access : BitVec 64}
    (context : FreshTransaction.Context origin source record bs heap FreshTransaction.remainingTables)
    (state : AccountAccess.AccessState source record access)
    (records : RunAttempt.InitializedRecords initialized origin cutoff ws bs) (before : cutoff.toNat≤record.toNat)
    (ready : AccountLookup.Environment origin) (refs : AccountLookup.References origin)
    (pointer : BitVec 64) (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word pointer)])
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "get_pre_state_account_optional") arguments continuation)=(some (.returned returned),post)) :
    ∃ target answer inner,AccountLookup.NormalResult initialized target cutoff ws bs record heap answer ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source target name answer) continuation=(some (.returned returned),inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called,addressCell⟩:=word_environment source.code.lookup (ofString "get_pre_state_account_optional") (ofString "addr") body .one pointer
    (original_code source.code context.runtime.code)
  obtain ⟨funded,target,answer,inner,bodyRun,checked,continued,endpoint⟩:=
    CallNormal.scoped_normal source post name .one (ofString "get_pre_state_account_optional") arguments _ body continuation callee .one args called returned normal
  have result:=body_normal (source:=callEntryStateHOLFinite source callee) (context.of_erase rfl) (state.of_erase rfl) records before ready refs addressCell answer bodyRun
  exact ⟨target,answer,inner,result,continued,endpoint⟩

end InitECandidate.Solver.Input.CurrentVerify.PreStateAccount

namespace InitECandidate.Solver.Input.CurrentVerify.AccountAccess
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The real transaction-cache miss returns the original complete pre-state
result, retaining its actual recorded tables and frame through the caller. -/
theorem after_miss_normal {origin initialized source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {record cutoff ws bs heap access pointer : BitVec 64}
    (context : FreshTransaction.Context origin source record bs heap FreshTransaction.remainingTables)
    (state : AccessState source record access)
    (records : RunAttempt.InitializedRecords initialized origin cutoff ws bs) (before : cutoff.toNat≤record.toNat)
    (ready : AccountLookup.Environment origin) (refs : AccountLookup.References origin)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word pointer)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterMiss=(some (.returned returned),post)) :
    AccountLookup.NormalResult initialized post cutoff ws bs record heap returned := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "addr"]=some [.val (.word pointer)]:=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,addressCell]
  rw [miss_shapes.2] at normal
  obtain ⟨target,answer,inner,result,continued,endpoint⟩:=PreStateAccount.scoped_normal context state records before ready refs pointer "a" [localVar "addr"]
    (.return (localVar "a")) args returned normal
  let current:=CallNormal.continuationEntry source target "a" answer
  have cell : current.locals.lookup (ofString "a")=some answer:=CallNormal.continuation_lookup_same _ _ _ _
  have expected : eval current (localVar "a")=some answer:=by simp [eval,evalHOLExact,localVar,toExact,cell]
  obtain ⟨read,postEq⟩:=return_normal current inner (localVar "a") returned continued
  have same : returned=answer:=Option.some.inj (read.symm.trans expected)
  have actual : LocalEffects.erase post=LocalEffects.erase target:=by rw [endpoint,postEq]; rfl
  rw [same]
  exact result.of_erase actual

/-- Complete unchanged first get_account_optional normal return. Its real
access insertion, cache miss and full pre-state getter produce the actual
account image and retain the recorded state used by later code lookup. -/
theorem body_normal {origin initialized source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {record cutoff ws bs heap pointer : BitVec 64}
    (context : FreshTransaction.Context origin source record bs heap FreshTransaction.tables)
    (records : RunAttempt.InitializedRecords initialized origin cutoff ws bs) (before : cutoff.toNat≤record.toNat)
    (ready : AccountLookup.Environment origin) (refs : AccountLookup.References origin)
    (addressCell : source.locals.lookup (ofString "addr")=some (.val (.word pointer)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    AccountLookup.NormalResult initialized post cutoff ws bs record heap returned := by
  rcases to_pre_state context addressCell _ normal with stopped|reached
  · exact (stopped.2 returned rfl).elim
  · obtain ⟨current,inner,last,currentAddress,forward,price,scope,continued,access,state⟩:=reached
    have result:=after_miss_normal last state records before ready refs currentAddress returned continued
    exact result.of_erase scope.metadata

/-- The actual enclosing first optional-account caller supplies its real
normal result, restored caller locals and actual continuation. -/
theorem scoped_normal {origin initialized source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {record cutoff ws bs heap : BitVec 64}
    (context : FreshTransaction.Context origin source record bs heap FreshTransaction.tables)
    (records : RunAttempt.InitializedRecords initialized origin cutoff ws bs) (before : cutoff.toNat≤record.toNat)
    (ready : AccountLookup.Environment origin) (refs : AccountLookup.References origin)
    (pointer : BitVec 64) (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word pointer)])
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "get_account_optional") arguments continuation)=(some (.returned returned),post)) :
    ∃ target answer inner,AccountLookup.NormalResult initialized target cutoff ws bs record heap answer ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source target name answer) continuation=(some (.returned returned),inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called,addressCell⟩:=word_environment source.code.lookup (ofString "get_account_optional") (ofString "addr") body .one pointer
    (original_code source.code context.runtime.code)
  obtain ⟨funded,target,answer,inner,bodyRun,checked,continued,endpoint⟩:=
    CallNormal.scoped_normal source post name .one (ofString "get_account_optional") arguments _ body continuation callee .one args called returned normal
  have result:=body_normal (source:=callEntryStateHOLFinite source callee) (context.of_erase rfl) records before ready refs addressCell answer bodyRun
  exact ⟨target,answer,inner,result,continued,endpoint⟩

end InitECandidate.Solver.Input.CurrentVerify.AccountAccess

#print axioms InitECandidate.Solver.Input.CurrentVerify.PreStateAccount.scoped_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountAccess.after_miss_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountAccess.body_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.AccountAccess.scoped_normal
