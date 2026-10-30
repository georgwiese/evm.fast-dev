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
    CurrentTable.New.ScalarEmpty source table spec.key spec.cap ∧ record.toNat+72≤table.toNat ∧ table.toNat+88≤heap.toNat

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
    (frame.memory record (by have before:=context.afterRecord; omega)).trans context.blockField,context.valid,?_,older,?_⟩
  · intro spec member
    obtain ⟨table,pointer,image,beforeTable,beforeHeap⟩:=context.images spec member
    have number:=record_address_number record context.recordArena spec.offset (context.valid spec member).2.1
    refine ⟨table,(frame.memory _ (by rw [number]; have before:=context.afterRecord; have inside:=(context.valid spec member).2.1; omega)).trans pointer,
      image.of_persistent beforeHeap frame.memory_frame,beforeTable,by omega⟩
  · intro name notHeap notRecord notCounter
    exact (frame.globals name notHeap).trans (context.globals name notHeap notRecord notCounter)

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
    by rw [memory]; exact context.blockField,context.valid,?_,context.older.of_erase origin source origin post record rfl same,?_⟩
  · intro spec member
    obtain ⟨table,pointer,image,beforeTable,beforeHeap⟩:=context.images spec member
    exact ⟨table,by rw [memory]; exact pointer,image.of_erase same,beforeTable,beforeHeap⟩
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
    context.older.put_global origin source record "journal_n" 0#64 (by decide),?_⟩
  · intro spec member
    obtain ⟨table,pointer,image,beforeTable,beforeHeap⟩:=context.images spec member
    exact ⟨table,pointer,image.of_memory rfl (by intros; rfl),beforeTable,beforeHeap⟩
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
    context.heapBound,context.heapAligned,context.afterRecord,?_,?_,?_,older,context.globals⟩
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
    · obtain ⟨oldTable,pointer,oldImage,oldBeforeTable,oldBeforeHeap⟩:=context.images old previous
      have fieldAway:=record_addresses_distinct record context.recordArena old.offset spec.offset
        (context.valid old previous).2.1 valid.2.1 (different old previous)
      refine ⟨oldTable,?_,keepImage oldTable old.key old.cap oldImage oldBeforeTable,oldBeforeTable,oldBeforeHeap⟩
      change StoreWord.put source.memory (record+BitVec.ofNat 64 spec.offset) table (record+BitVec.ofNat 64 old.offset)=.word oldTable
      rw [StoreWord.put,if_neg fieldAway]
      exact pointer
    · have same : old=spec:=by simpa only [List.mem_singleton] using last
      subst old
      exact ⟨table,by simp [written,StoreWord.put],keepImage table spec.key spec.cap image beforeTable,beforeTable,beforeHeap⟩

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
      heap image context.afterRecord beforeHeap tableCell storeRun
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
    heap currentImage context.afterRecord beforeHeap tableCell storeRun
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
      current.bounded,current.aligned,before,?_,?_,?_,older,?_⟩
    · simp [StoreWord.put]
    · intro spec impossible; cases impossible
    · intro spec impossible; cases impossible
    · intro name notHeap notRecord notCounter
      exact globals name notRecord notHeap
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

end InitECandidate.Solver.Input.CurrentVerify.UncheckedSystem

#print axioms InitECandidate.Solver.Input.CurrentVerify.UncheckedSystem.original_code
#print axioms InitECandidate.Solver.Input.CurrentVerify.UncheckedSystem.after_fresh_shape
#print axioms InitECandidate.Solver.Input.CurrentVerify.UncheckedSystem.fresh_physical_trace
