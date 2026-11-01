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
    ∃ db node,source.memory (ws+24#64)=.word node ∧
      ∃ registry : Mpt.WitnessCore.NodeRegistry source (ws.toNat+40) bs db,registry.graph.valid node := by
  obtain ⟨db,node,cell,registry,member⟩:=state.initialized.world
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
  refine ⟨db,node,rootMemory.trans cell,⟨graph,values,regions,disjoint⟩,?_⟩
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
    ∃ db node,source.memory (ws+24#64)=.word node ∧
      ∃ registry : Mpt.WitnessCore.NodeRegistry source (ws.toNat+40) bs db,
        registry.graph.valid node ∧ registry.graph.Protected 2701134704#64 ∧
        Mpt.TrieWalk.ValueProtected registry.graph 2701134704#64 := by
  obtain ⟨db,node,stored,registry,member⟩:=state.world
  refine ⟨db,node,stored,registry,member,?_,?_⟩
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
    endian.trans ready.little,by rw [globals]; exact ready.nibbles⟩

end InitECandidate.Solver.Input.CurrentVerify.AccountLookup

namespace InitECandidate.Solver.Input.CurrentVerify
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The real main input producer already derives every lookup workspace
cell; extracting them does not assume any later account execution. -/
theorem Data.account_lookup_environment {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary) :
    AccountLookup.Environment source := ⟨data.keccak,data.little,data.mptNibs⟩

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
    endian.trans ready.little,(context.globals _ (by decide) (by decide) (by decide)).trans ready.nibbles⟩

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
  world : ∃ db node,source.memory (ws+24#64)=.word node ∧
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
  obtain ⟨db,node,stored,registry,member⟩:=entry.world
  obtain ⟨graph,validEq,regions,disjoint,⟨values⟩⟩:=registry.graph.after_agreement source target 1024 (ws.toNat+40) bs.toNat (Mpt.WitnessCore.WitnessValue db)
    registry.values registry.regions registry.disjoint domain (fun _ _=>congrFun memory _) (fun _ _=>congrFun memory _)
  refine ⟨db,node,(congrFun memory _).trans stored,⟨graph,values,regions,disjoint⟩,?_⟩
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
