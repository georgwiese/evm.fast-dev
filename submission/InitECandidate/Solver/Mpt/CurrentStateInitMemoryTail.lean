import InitECandidate.Solver.Input.GlobalEffectsGlobalCall
import InitECandidate.Solver.WitnessRadix.AllocationGlobals
import InitECandidate.Solver.Input.CurrentTable.NewScalarImage
import InitECandidate.Solver.Mpt.CurrentStateInitMemorySuffix

namespace InitECandidate.Solver.Mpt.StateInit.MemorySuffix
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The same real table call supplies the scalar immediately stored in
its fresh block-state field. Both memory frames use the entering frontier. -/
theorem Tail.table_store (frontier ws bs : BitVec 64) (key cap offset : Nat) (inside : offset≤72)
    (capLower : 2≤(BitVec.ofNat 64 cap).toNat) (continuation : ProgHOL 64) (tail : Tail frontier ws bs continuation) :
    Tail frontier ws bs (tableStore key cap offset continuation) := by
  intro source post context value normal
  have safe : LocalPrefix (ofString "_") (tableCall key cap):=
    .call (some (ofString "t")) _ _ (by intro name same; cases Option.some.inj same; decide)
  obtain ⟨middle,firstRun,continued,preserved⟩:=safe.normal_continue source post (.seq (.store (field "bs" offset) (localVar "t")) continuation) value normal
  obtain ⟨heap,heapCell,heapArena,heapBound,heapAligned,before⟩:=context.heap_at_bs
  obtain ⟨tableCell,otherLocals,tableArena,physical⟩:=CurrentTable.New.scalar_local_normal_frame source middle "t"
    (BitVec.ofNat 64 key) (BitVec.ofNat 64 cap) heap [.const (BitVec.ofNat 64 key),.const (BitVec.ofNat 64 cap)] rfl capLower
    heapCell heapArena heapBound heapAligned context.arena firstRun
  have current:=context.after_persistent physical (Nat.le_trans context.bsFresh.1 before) heapCell
  have first:=physical.memory_frame.weaken source middle heap bs before
  have tableRead : eval middle (localVar "t")=some (.val (.word heap)):=by simp [eval,evalHOLExact,localVar,toExact,tableCell]
  obtain ⟨valueEq,finalArena,last⟩:=store_suffix_normal middle post frontier ws bs current offset inside (localVar "t") heap tableRead continuation tail value continued
  exact ⟨valueEq,finalArena,first.trans source middle post bs bs last (Nat.le_refl _)⟩

theorem Tail.stored_constant (frontier ws bs : BitVec 64) (offset : Nat) (inside : offset≤72)
    (word : BitVec 64) (continuation : ProgHOL 64) (tail : Tail frontier ws bs continuation) :
    Tail frontier ws bs (.seq (.store (field "bs" offset) (.const word)) continuation) := by
  intro source post context value normal
  exact store_suffix_normal source post frontier ws bs context offset inside (.const word) word rfl continuation tail value normal

theorem Tail.stored_workspace (frontier ws bs : BitVec 64) (continuation : ProgHOL 64) (tail : Tail frontier ws bs continuation) :
    Tail frontier ws bs (.seq (.store (field "bs" 0) (.var .global (ofString "ws"))) continuation) := by
  intro source post context value normal
  have read : eval source (.var .global (ofString "ws"))=some (.val (.word ws)):=by simp [eval,evalHOLExact,context.wsCell]
  exact store_suffix_normal source post frontier ws bs context 0 (by decide) _ ws read continuation tail value normal

theorem finish_frame (frontier ws bs : BitVec 64) : Tail frontier ws bs finish := by
  apply Tail.global_constant frontier ws bs "journal_n" 0#64 _ (by decide) (by decide) (by decide) (by decide) (by decide)
  apply Tail.global_constant frontier ws bs "ts" 0#64 _ (by decide) (by decide) (by decide) (by decide) (by decide)
  exact Tail.returned frontier ws bs

/-- The actual journal capacity assignment supplies its own typed global
for the following multiplication/allocation. Old global contents are not an
entry premise, and allocation room still comes from its actual return. -/
theorem journal_frame (frontier ws bs : BitVec 64) : Tail frontier ws bs journal := by
  intro source post context value normal
  have safe : LocalPrefix (ofString "_") (.assign .global (ofString "journal_cap") (.const 524288#64)):=.globalAssign _ _
  obtain ⟨middle,firstRun,continued,preserved⟩:=safe.normal_continue source post _ value normal
  have endpoint:=global_assign_none source middle "journal_cap" (.const 524288#64) 524288#64 rfl firstRun
  have current : MemoryContext middle frontier ws bs:=by
    rw [endpoint]
    exact context.put_global "journal_cap" 524288#64 (by decide) (by decide) (by decide) (by decide) (by decide)
  have first : PersistentMemoryFrame source middle bs:=by
    rw [endpoint]
    exact PersistentMemoryFrame.put_global source source bs ⟨context.heap_at_bs,rfl,by intros; rfl⟩ "journal_cap" 524288#64 (by decide)
  have capCell : middle.globals.lookup (ofString "journal_cap")=some (.val (.word 524288#64)):=by
    rw [endpoint]
    exact putGlobal.lookup_same _ _ _
  have args : evalListHOLFinite middle (h:=fun query=>Classical.propDecidable (middle.memaddrs query))
      [.panop .mul [.var .global (ofString "journal_cap"),.const 32#64]]=some (PersistentAlloc.values 16777216#64) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capCell,valueIsWord,valueWord,panOpHOL,PersistentAlloc.values]
  obtain ⟨valueEq,finalArena,last⟩:=allocate_suffix_normal middle post frontier ws bs current "journal" 16777216#64 _ finish args
    (by decide) (by decide) (by decide) (by decide) (by decide) (finish_frame frontier ws bs) value continued
  exact ⟨valueEq,finalArena,first.trans source middle post bs bs last (Nat.le_refl _)⟩

theorem scratch_frame (frontier ws bs : BitVec 64) : Tail frontier ws bs scratch := by
  intro source post context value normal
  exact allocate_suffix_normal source post frontier ws bs context "sk_buf" 64#64 [.const 64#64] journal rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (journal_frame frontier ws bs) value normal

/-- Every actual normal block-state suffix preserves the original earlier
memory below BS and complete runtime metadata while initializing its real tables,
scratch buffer and16MiB journal. No allocation success is assumed. -/
theorem after_block_allocation_frame (frontier ws bs : BitVec 64) : Tail frontier ws bs afterBlockAllocation := by
  rw [shape]
  apply Tail.stored_workspace
  apply Tail.table_store frontier ws bs 20 256 8 (by decide) (by decide)
  apply Tail.table_store frontier ws bs 20 256 16 (by decide) (by decide)
  apply Tail.table_store frontier ws bs 52 256 24 (by decide) (by decide)
  apply Tail.table_store frontier ws bs 20 64 32 (by decide) (by decide)
  apply Tail.table_store frontier ws bs 52 64 40 (by decide) (by decide)
  apply Tail.table_store frontier ws bs 32 64 48 (by decide) (by decide)
  apply Tail.stored_constant frontier ws bs 56 (by decide) 0#64
  apply Tail.stored_constant frontier ws bs 64 (by decide) 0#64
  apply Tail.table_store frontier ws bs 20 256 72 (by decide) (by decide)
  exact scratch_frame frontier ws bs

end InitECandidate.Solver.Mpt.StateInit.MemorySuffix

#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.Tail.table_store
#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.journal_frame
#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.after_block_allocation_frame

namespace InitECandidate.Solver.Mpt.StateInit.MemorySuffix.BlockTables
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

structure Spec where
  key : Nat
  cap : Nat
  offset : Nat
  deriving DecidableEq

def Spec.Valid (spec : Spec) : Prop:=8≤spec.offset ∧ spec.offset≤72 ∧ spec.offset%8=0 ∧ 2≤(BitVec.ofNat 64 spec.cap).toNat

def Images (source : PanSemStateFiniteExact 64 Guest.HostMemory) (bs heap : BitVec 64) (done : List Spec) : Prop:=
  ∀ spec∈done,∃ table,source.memory (bs+BitVec.ofNat 64 spec.offset)=.word table ∧
    CurrentTable.New.ScalarEmpty source table (BitVec.ofNat 64 spec.key) (BitVec.ofNat 64 spec.cap) ∧
    bs.toNat+80≤table.toNat ∧ (CurrentTable.New.scalarNextHeap table (BitVec.ofNat 64 spec.key) (BitVec.ofNat 64 spec.cap)).toNat≤heap.toNat

def Separated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (bs : BitVec 64) (done : List Spec) : Prop:=
  ∀ left∈done,∀ right∈done,left.offset≠right.offset→∃ l r,
    source.memory (bs+BitVec.ofNat 64 left.offset)=.word l ∧ source.memory (bs+BitVec.ofNat 64 right.offset)=.word r ∧
      ((CurrentTable.New.scalarNextHeap l (BitVec.ofNat 64 left.key) (BitVec.ofNat 64 left.cap)).toNat≤r.toNat ∨
       (CurrentTable.New.scalarNextHeap r (BitVec.ofNat 64 right.key) (BitVec.ofNat 64 right.cap)).toNat≤l.toNat)

theorem Separated.of_memory {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {bs : BitVec 64} {done : List Spec}
    (state : Separated source bs done)
    (memory : ∀ spec∈done,target.memory (bs+BitVec.ofNat 64 spec.offset)=source.memory (bs+BitVec.ofNat 64 spec.offset)) : Separated target bs done := by
  intro left lm right rm different
  obtain ⟨l,r,lc,rc,split⟩:=state left lm right rm different
  exact ⟨l,r,(memory left lm).trans lc,(memory right rm).trans rc,split⟩

/-- Only already constructed table images are tracked. The base physical
context remains valid before any of these actual allocations takes place. -/
structure Context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frontier ws bs heap : BitVec 64) (done : List Spec) : Prop where
  memory : MemoryContext source frontier ws bs
  heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  valid : ∀ spec∈done,spec.Valid
  images : Images source bs heap done
  separated : Separated source bs done

theorem Context.heap_facts {source : PanSemStateFiniteExact 64 Guest.HostMemory} {frontier ws bs heap : BitVec 64} {done : List Spec}
    (state : Context source frontier ws bs heap done) :
    AllocatedBytes.Arena heap 0 ∧ heap.toNat≤2952790016 ∧ heap.toNat%8=0 ∧ frontier.toNat≤heap.toNat ∧ bs.toNat+80≤heap.toNat := by
  obtain ⟨cursor,cell,owned,bounded,aligned,before⟩:=state.memory.heap
  have same : cursor=heap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (cell.symm.trans state.heapCell)))
  subst cursor
  obtain ⟨old,oldCell,afterBs,oldBound,oldAlign⟩:=state.memory.afterBs
  have oldEq : old=heap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (oldCell.symm.trans state.heapCell)))
  subst old
  exact ⟨owned,bounded,aligned,before,afterBs⟩

theorem Context.empty {source : PanSemStateFiniteExact 64 Guest.HostMemory} {frontier ws bs heap : BitVec 64}
    (physical : MemoryContext source frontier ws bs) (cell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) : Context source frontier ws bs heap [] := by
  refine ⟨physical,cell,?_,?_,?_⟩
  · intro spec member; cases member
  · intro spec member; cases member
  · intro left member; cases member

theorem Context.of_erase {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {frontier ws bs heap : BitVec 64} {done : List Spec}
    (state : Context source frontier ws bs heap done) (same : LocalEffects.erase target=LocalEffects.erase source) : Context target frontier ws bs heap done := by
  have globals:=congrArg PanSemStateFiniteExact.globals same
  change target.globals=source.globals at globals
  have memory:=LocalEffects.memory_of_erase source target same
  refine ⟨state.memory.of_frame same,by rw [globals]; exact state.heapCell,state.valid,?_,state.separated.of_memory (by intros; rw [memory])⟩
  intro spec member
  obtain ⟨table,field,image,afterBs,beforeHeap⟩:=state.images spec member
  exact ⟨table,(congrFun memory _).trans field,image.of_erase same,afterBs,beforeHeap⟩

/-- A later actual persistent allocation protects all earlier table headers
and block-state pointer fields, while deriving its own new live heap. -/
theorem Context.after_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {frontier ws bs heap : BitVec 64} {done : List Spec}
    (state : Context source frontier ws bs heap done) (physical : MemoryContext target frontier ws bs)
    (frame : PersistentMemoryFrame source target heap) : ∃ next,Context target frontier ws bs next done := by
  obtain ⟨next,cell,owned,bounded,aligned,grows⟩:=frame.nextHeap
  have bsBefore:=state.heap_facts.2.2.2.2
  have recordMemory (spec : Spec) (member : spec∈done) : target.memory (bs+BitVec.ofNat 64 spec.offset)=source.memory (bs+BitVec.ofNat 64 spec.offset):=by
    apply frame.memory
    have number:=byteAddress_toNat bs spec.offset (by have upper:=state.memory.bsArena.upper; have small:=(state.valid spec member).2.1; omega)
    change (bs+BitVec.ofNat 64 spec.offset).toNat=bs.toNat+spec.offset at number
    rw [number]
    have small:=(state.valid spec member).2.1
    omega
  refine ⟨next,⟨physical,cell,state.valid,?_,state.separated.of_memory recordMemory⟩⟩
  intro spec member
  obtain ⟨table,field,image,afterBs,beforeHeap⟩:=state.images spec member
  have beforeHeader : table.toNat+88≤heap.toNat:=by have endBefore:=image.geometry.header_before_end; omega
  exact ⟨table,(recordMemory spec member).trans field,image.of_persistent beforeHeader frame,afterBs,Nat.le_trans beforeHeap grows⟩

/-- An actual distinct block-state field store preserves every initialized
table image and pointer; the store's mapping/effect come from its own run. -/
theorem Context.store {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {frontier ws bs heap : BitVec 64} {done : List Spec}
    (state : Context source frontier ws bs heap done) (offset : Nat) (inside : offset≤72)
    (different : ∀ spec∈done,offset≠spec.offset) (expression : ExpHOL 64) (word : BitVec 64)
    (read : eval source expression=some (.val (.word word)))
    (normal : evaluateHOLFiniteState source (.store (field "bs" offset) expression)=(none,target)) :
    Context target frontier ws bs heap done ∧ target.memory (bs+BitVec.ofNat 64 offset)=.word word ∧
      ∀ spec∈done,target.memory (bs+BitVec.ofNat 64 spec.offset)=source.memory (bs+BitVec.ofNat 64 spec.offset) := by
  have addressRead : eval source (field "bs" offset)=some (.val (.word (bs+BitVec.ofNat 64 offset))):=by
    simp [eval,field,evalHOLExact,evalListHOLExact,state.memory.bsCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have number:=byteAddress_toNat bs offset (by have upper:=state.memory.bsArena.upper; omega)
  change (bs+BitVec.ofNat 64 offset).toNat=bs.toNat+offset at number
  obtain ⟨current,frame⟩:=state.memory.word_store (field "bs" offset) expression _ word addressRead read (by rw [number]; have before:=state.memory.bsFresh.1; omega) normal
  obtain ⟨mapped,endpoint⟩:=word_store_normal source target _ _ _ _ addressRead read normal
  have domain : target.memaddrs=source.memaddrs:=by rw [endpoint]
  have recordMemory (spec : Spec) (member : spec∈done) : target.memory (bs+BitVec.ofNat 64 spec.offset)=source.memory (bs+BitVec.ofNat 64 spec.offset):=by
    have small:=(state.valid spec member).2.1
    have away : bs+BitVec.ofNat 64 spec.offset≠bs+BitVec.ofNat 64 offset:=by
      intro same
      have equal:=congrArg BitVec.toNat ((BitVec.add_right_inj bs).mp same)
      rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at equal
      exact different spec member equal.symm
    rw [endpoint]
    exact if_neg away
  refine ⟨⟨current,by rw [endpoint]; exact state.heapCell,state.valid,?_,state.separated.of_memory recordMemory⟩,?_,recordMemory⟩
  · intro spec member
    obtain ⟨table,cell,image,afterBs,beforeHeap⟩:=state.images spec member
    have currentImage : CurrentTable.New.ScalarEmpty target table (BitVec.ofNat 64 spec.key) (BitVec.ofNat 64 spec.cap):=by
      apply image.of_memory domain
      intro entry entryMember
      have lower:=CurrentTable.New.scalar_write_lower table _ _ entry image.geometry.table entryMember
      have away : entry.1≠bs+BitVec.ofNat 64 offset:=by intro same; have equal:=congrArg BitVec.toNat same; rw [number] at equal; omega
      rw [endpoint]
      exact if_neg away
    exact ⟨table,(recordMemory spec member).trans cell,currentImage,afterBs,beforeHeap⟩
  · rw [endpoint]
    simp [StoreWord.put]

end InitECandidate.Solver.Mpt.StateInit.MemorySuffix.BlockTables

#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.BlockTables.Separated.of_memory
#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.BlockTables.Context.heap_facts
#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.BlockTables.Context.empty
#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.BlockTables.Context.of_erase
#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.BlockTables.Context.after_frame
#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.BlockTables.Context.store

namespace InitECandidate.Solver.Mpt.StateInit.MemorySuffix.BlockTables
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- A real unrelated global assignment retains the constructed block tables. -/
theorem Context.put_global {source : PanSemStateFiniteExact 64 Guest.HostMemory} {frontier ws bs heap : BitVec 64} {done : List Spec}
    (state : Context source frontier ws bs heap done) (name : String) (word : BitVec 64)
    (notHeap : ofString "heap_ptr"≠ofString name) (notWs : ofString "ws"≠ofString name) (notBs : ofString "bs"≠ofString name)
    (notScratch : ofString "scratch_ptr"≠ofString name) (notFrame : ofString "frame_mem_ptr"≠ofString name) :
    Context (putGlobal source name word) frontier ws bs heap done := by
  refine ⟨state.memory.put_global name word notHeap notWs notBs notScratch notFrame,
    (putGlobal.lookup_other source name word _ notHeap).trans state.heapCell,state.valid,?_,state.separated.of_memory (by intros; rfl)⟩
  intro spec member
  obtain ⟨table,field,image,afterBs,beforeHeap⟩:=state.images spec member
  exact ⟨table,field,image.of_memory rfl (by intros; rfl),afterBs,beforeHeap⟩

/-- The actual normal global allocator supplies a strong earlier-memory
frame at its own entering heap, so every initialized table remains valid. -/
theorem Context.allocate_global {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {frontier ws bs heap : BitVec 64} {done : List Spec}
    (state : Context source frontier ws bs heap done) (name : String) (amount : BitVec 64) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (PersistentAlloc.values amount))
    (notHeap : ofString "heap_ptr"≠ofString name) (notWs : ofString "ws"≠ofString name) (notBs : ofString "bs"≠ofString name)
    (notScratch : ofString "scratch_ptr"≠ofString name) (notFrame : ofString "frame_mem_ptr"≠ofString name)
    (normal : evaluateHOLFiniteState source (allocate name arguments)=(none,post)) : ∃ next,Context post frontier ws bs next done := by
  obtain ⟨physical,broad⟩:=state.memory.allocate_global name amount arguments args notHeap notWs notBs notScratch notFrame normal
  have facts:=state.heap_facts
  obtain ⟨room,funded,endpoint⟩:=PersistentAlloc.global_call_normal_any source post name heap amount arguments args
    (PersistentAlloc.original_code source.code state.memory.arena.code) (Input.Trap.original_code source.code state.memory.arena.code) state.heapCell facts.2.1 normal
  let allocated:=PersistentAlloc.post {source with clock:=source.clock-1} heap amount
  have first : PersistentNormalFrame source allocated heap:=
    (PersistentAlloc.post_persistent_frame {source with clock:=source.clock-1} heap amount facts.1 room).of_erase _ _ source allocated heap rfl rfl
  have strong : PersistentMemoryFrame source post heap:=by
    rw [endpoint]
    exact first.memory_frame.put_global source allocated heap name heap notHeap
  exact state.after_frame physical strong

/-- Same actual table constructor and following BS field store extend the
partial initialized-image context. Older tables lie before the new table's
real entering heap, so full allocation separation is derived too. -/
theorem Context.table {source middle target : PanSemStateFiniteExact 64 Guest.HostMemory} {frontier ws bs heap : BitVec 64} {done : List Spec}
    (state : Context source frontier ws bs heap done) (spec : Spec) (valid : spec.Valid)
    (different : ∀ old∈done,spec.offset≠old.offset)
    (called : evaluateHOLFiniteState source (tableCall spec.key spec.cap)=(none,middle))
    (stored : evaluateHOLFiniteState middle (.store (field "bs" spec.offset) (localVar "t"))=(none,target)) :
    Context target frontier ws bs (CurrentTable.New.scalarNextHeap heap (BitVec.ofNat 64 spec.key) (BitVec.ofNat 64 spec.cap)) (spec::done) := by
  have facts:=state.heap_facts
  obtain ⟨tableCell,image,nextCell,physical⟩:=CurrentTable.New.local_scalar_empty source middle "t" (BitVec.ofNat 64 spec.key) (BitVec.ofNat 64 spec.cap) heap
    [.const (BitVec.ofNat 64 spec.key),.const (BitVec.ofNat 64 spec.cap)] rfl valid.2.2.2 state.heapCell facts.1 facts.2.1 facts.2.2.1 state.memory.arena called
  have middleMemory:=state.memory.after_persistent physical facts.2.2.2.1 state.heapCell
  obtain ⟨cursor,middleState⟩:=state.after_frame middleMemory physical.memory_frame
  have cursorEq : cursor=CurrentTable.New.scalarNextHeap heap (BitVec.ofNat 64 spec.key) (BitVec.ofNat 64 spec.cap):=
    HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (middleState.heapCell.symm.trans nextCell)))
  subst cursor
  have read:=Request.local_word middle "t" heap tableCell
  obtain ⟨storedState,fieldCell,recordFrame⟩:=middleState.store spec.offset valid.2.1 different (localVar "t") heap read stored
  have addressRead : eval middle (field "bs" spec.offset)=some (.val (.word (bs+BitVec.ofNat 64 spec.offset))):=by
    simp [eval,field,evalHOLExact,evalListHOLExact,middleMemory.bsCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  obtain ⟨mapped,endpoint⟩:=word_store_normal middle target _ _ _ _ addressRead read stored
  have number:=byteAddress_toNat bs spec.offset (by have upper:=state.memory.bsArena.upper; have small:=valid.2.1; omega)
  change (bs+BitVec.ofNat 64 spec.offset).toNat=bs.toNat+spec.offset at number
  have newImage : CurrentTable.New.ScalarEmpty target heap (BitVec.ofNat 64 spec.key) (BitVec.ofNat 64 spec.cap):=by
    apply image.of_memory (by rw [endpoint])
    intro entry member
    have lower:=CurrentTable.New.scalar_write_lower heap _ _ entry image.geometry.table member
    have away : entry.1≠bs+BitVec.ofNat 64 spec.offset:=by
      intro same
      have equal:=congrArg BitVec.toNat same
      rw [number] at equal
      have before:=facts.2.2.2.2
      have small:=valid.2.1
      omega
    rw [endpoint]
    exact if_neg away
  have sameField (old : Spec) (member : old∈done) : target.memory (bs+BitVec.ofNat 64 old.offset)=source.memory (bs+BitVec.ofNat 64 old.offset):=by
    rw [recordFrame old member]
    apply physical.memory
    have small:=(state.valid old member).2.1
    have oldNumber:=byteAddress_toNat bs old.offset (by have upper:=state.memory.bsArena.upper; omega)
    change (bs+BitVec.ofNat 64 old.offset).toNat=bs.toNat+old.offset at oldNumber
    rw [oldNumber]
    have before:=facts.2.2.2.2
    omega
  refine ⟨storedState.memory,storedState.heapCell,?_,?_,?_⟩
  · intro old member
    rcases List.mem_cons.mp member with rfl|member
    · exact valid
    · exact state.valid old member
  · intro old member
    rcases List.mem_cons.mp member with rfl|member
    · exact ⟨heap,fieldCell,newImage,facts.2.2.2.2,Nat.le_refl _⟩
    · exact storedState.images old member
  · intro left lm right rm notSame
    rcases List.mem_cons.mp lm with sameLeft|oldLeftMember
    · subst left
      rcases List.mem_cons.mp rm with sameRight|oldRightMember
      · subst right
        exact (notSame rfl).elim
      · obtain ⟨oldTable,oldField,oldImage,oldAfter,oldBefore⟩:=state.images right oldRightMember
        exact ⟨heap,oldTable,fieldCell,(sameField right oldRightMember).trans oldField,Or.inr oldBefore⟩
    · rcases List.mem_cons.mp rm with sameRight|oldRightMember
      · subst right
        obtain ⟨oldTable,oldField,oldImage,oldAfter,oldBefore⟩:=state.images left oldLeftMember
        exact ⟨oldTable,heap,(sameField left oldLeftMember).trans oldField,fieldCell,Or.inl oldBefore⟩
      · exact storedState.separated left oldLeftMember right oldRightMember notSame

end InitECandidate.Solver.Mpt.StateInit.MemorySuffix.BlockTables

#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.BlockTables.Context.put_global
#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.BlockTables.Context.allocate_global
#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.BlockTables.Context.table

namespace InitECandidate.Solver.Mpt.StateInit.MemorySuffix.BlockTables
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

/-- The original final globals and return retain the complete current
block-table images without asserting any future allocation or access. -/
theorem Context.finish_normal {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {frontier ws bs heap : BitVec 64} {done : List Spec}
    (state : Context source frontier ws bs heap done) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source finish=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ Context post frontier ws bs heap done := by
  rw [finish] at normal
  have firstSafe : LocalPrefix (ofString "_") (.assign .global (ofString "journal_n") (.const 0#64)):=.globalAssign _ _
  obtain ⟨middle,firstRun,continued,preserved⟩:=firstSafe.normal_continue source post _ value normal
  have firstEndpoint:=global_assign_none source middle "journal_n" (.const 0#64) 0#64 rfl firstRun
  have current : Context middle frontier ws bs heap done:=by
    rw [firstEndpoint]
    exact state.put_global "journal_n" 0#64 (by decide) (by decide) (by decide) (by decide) (by decide)
  have secondSafe : LocalPrefix (ofString "_") (.assign .global (ofString "ts") (.const 0#64)):=.globalAssign _ _
  obtain ⟨last,secondRun,returnedRun,preserved⟩:=secondSafe.normal_continue middle post (.return (.const 0#64)) value continued
  have secondEndpoint:=global_assign_none middle last "ts" (.const 0#64) 0#64 rfl secondRun
  have lastState : Context last frontier ws bs heap done:=by
    rw [secondEndpoint]
    exact current.put_global "ts" 0#64 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨read,endpoint⟩:=return_normal last post (.const 0#64) value returnedRun
  exact ⟨Option.some.inj read.symm,lastState.of_erase (by rw [endpoint] <;> rfl)⟩

/-- The real journal suffix writes its own globals and heap, preserving
exactly the earlier sk_buf allocation on every outcome. -/
theorem journal_key_buffer_global (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (ofString "sk_buf") code journal := by
  rw [journal]
  apply GlobalEffects.sequence _ code _ _ (GlobalEffects.global_other _ code _ _ (by decide))
  apply GlobalEffects.sequence _ code _ _
    (GlobalEffects.global_call_body _ code (ofString "journal") (ofString "alloc") _ PersistentAlloc.formals PersistentAlloc.body .one
      (by decide) (PersistentAlloc.original_code code installed) (PersistentAlloc.globals _ code installed (by decide)))
  rw [finish]
  exact GlobalEffects.sequence _ code _ _ (GlobalEffects.global_other _ code _ _ (by decide))
    (GlobalEffects.sequence _ code _ _ (GlobalEffects.global_other _ code _ _ (by decide)) (GlobalEffects.returned _ code _))

/-- Actual key-buffer allocation retained with the final real heap. Its
record interval is after BS and entirely before the initializer's end. -/
def KeyBuffer (source : PanSemStateFiniteExact 64 Guest.HostMemory) (bs : BitVec 64) : Prop:=
  ∃ buffer heap,source.globals.lookup (ofString "sk_buf")=some (.val (.word buffer)) ∧
    AllocatedBytes.Arena buffer 64 ∧ buffer.toNat%8=0 ∧ bs.toNat+80≤buffer.toNat ∧
    source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧ buffer.toNat+64≤heap.toNat

theorem KeyBuffer.of_erase {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {bs : BitVec 64}
    (buffer : KeyBuffer source bs) (same : LocalEffects.erase target=LocalEffects.erase source) : KeyBuffer target bs := by
  have globals:=congrArg PanSemStateFiniteExact.globals same
  change target.globals=source.globals at globals
  obtain ⟨pointer,heap,cell,arena,aligned,afterBlock,heapCell,beforeHeap⟩:=buffer
  exact ⟨pointer,heap,by rw [globals]; exact cell,arena,aligned,afterBlock,by rw [globals]; exact heapCell,beforeHeap⟩

/-- Real journal capacity assignment/allocation advances its own heap and
retains every block-table image through the actual normal final return. -/
theorem Context.journal_normal_grows {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {frontier ws bs heap : BitVec 64} {done : List Spec}
    (state : Context source frontier ws bs heap done) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source journal=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ ∃ next,Context post frontier ws bs next done ∧ heap.toNat≤next.toNat := by
  rw [journal] at normal
  have safe : LocalPrefix (ofString "_") (.assign .global (ofString "journal_cap") (.const 524288#64)):=.globalAssign _ _
  obtain ⟨middle,assigned,continued,preserved⟩:=safe.normal_continue source post _ value normal
  have endpoint:=global_assign_none source middle "journal_cap" (.const 524288#64) 524288#64 rfl assigned
  have current : Context middle frontier ws bs heap done:=by
    rw [endpoint]
    exact state.put_global "journal_cap" 524288#64 (by decide) (by decide) (by decide) (by decide) (by decide)
  have capCell : middle.globals.lookup (ofString "journal_cap")=some (.val (.word 524288#64)):=by
    rw [endpoint]
    exact putGlobal.lookup_same _ _ _
  have args : evalListHOLFinite middle (h:=fun query=>Classical.propDecidable (middle.memaddrs query))
      [.panop .mul [.var .global (ofString "journal_cap"),.const 32#64]]=some (PersistentAlloc.values 16777216#64):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capCell,valueIsWord,valueWord,panOpHOL,PersistentAlloc.values]
  have allocSafe : LocalPrefix (ofString "_") (allocate "journal" [.panop .mul [.var .global (ofString "journal_cap"),.const 32#64]]):=.globalCall _ _ _
  obtain ⟨last,allocated,finished,preserved⟩:=allocSafe.normal_continue middle post finish value continued
  obtain ⟨next,lastState⟩:=current.allocate_global "journal" 16777216#64 _ args (by decide) (by decide) (by decide) (by decide) (by decide) allocated
  obtain ⟨answer,finalState⟩:=lastState.finish_normal value finished
  have facts:=current.heap_facts
  obtain ⟨room,funded,allocation⟩:=PersistentAlloc.global_call_normal_any middle last "journal" heap 16777216#64 _ args
    (PersistentAlloc.original_code middle.code current.memory.arena.code) (Input.Trap.original_code middle.code current.memory.arena.code)
    current.heapCell facts.2.1 allocated
  have allocatedCell : last.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 16777216#64))):=by
    rw [allocation]
    simp [PersistentAlloc.post,putGlobal,HolFiniteMapExact.update,FUPDATE,show ofString "journal"≠ofString "heap_ptr" from by decide]
  have nextEq : next=PersistentAlloc.rounded heap 16777216#64:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (lastState.heapCell.symm.trans allocatedCell)))
  have grows:=(PersistentAlloc.guards heap 16777216#64 room).2.2.1
  exact ⟨answer,next,finalState,by rw [nextEq]; omega⟩

theorem Context.journal_normal {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {frontier ws bs heap : BitVec 64} {done : List Spec}
    (state : Context source frontier ws bs heap done) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source journal=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ ∃ next,Context post frontier ws bs next done := by
  obtain ⟨answer,next,complete,grows⟩:=state.journal_normal_grows value normal
  exact ⟨answer,next,complete⟩

/-- The actual scratch and journal suffix retains all already initialized
block tables, deriving both allocations from this same normal execution. -/
theorem Context.scratch_normal_key {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {frontier ws bs heap : BitVec 64} {done : List Spec}
    (state : Context source frontier ws bs heap done) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source scratch=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ ∃ next,Context post frontier ws bs next done ∧ KeyBuffer post bs := by
  rw [scratch] at normal
  have safe : LocalPrefix (ofString "_") (allocate "sk_buf" [.const 64#64]):=.globalCall _ _ _
  obtain ⟨middle,allocated,continued,preserved⟩:=safe.normal_continue source post journal value normal
  obtain ⟨next,current⟩:=state.allocate_global "sk_buf" 64#64 [.const 64#64] rfl (by decide) (by decide) (by decide) (by decide) (by decide) allocated
  obtain ⟨answer,last,complete,grows⟩:=current.journal_normal_grows value continued
  have facts:=state.heap_facts
  obtain ⟨room,funded,allocation⟩:=PersistentAlloc.global_call_normal_any source middle "sk_buf" heap 64#64 [.const 64#64] rfl
    (PersistentAlloc.original_code source.code state.memory.arena.code) (Input.Trap.original_code source.code state.memory.arena.code)
    state.heapCell facts.2.1 allocated
  have cell : middle.globals.lookup (ofString "sk_buf")=some (.val (.word heap)):=by
    rw [allocation]
    exact putGlobal.lookup_same _ _ _
  have allocatedCell : middle.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 64#64))):=by
    rw [allocation]
    simp [PersistentAlloc.post,putGlobal,HolFiniteMapExact.update,FUPDATE,show ofString "sk_buf"≠ofString "heap_ptr" from by decide]
  have nextEq : next=PersistentAlloc.rounded heap 64#64:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (current.heapCell.symm.trans allocatedCell)))
  have allocatedEnd:=(PersistentAlloc.guards heap 64#64 room).2.2.1
  change heap.toNat+64≤(PersistentAlloc.rounded heap 64#64).toNat at allocatedEnd
  have preserved:=journal_key_buffer_global middle.code current.memory.arena.code middle rfl
  rw [continued] at preserved
  have finalCell : post.globals.lookup (ofString "sk_buf")=some (.val (.word heap)):=
    (congrArg Prod.snd preserved).trans cell
  exact ⟨answer,last,complete,heap,last,finalCell,⟨facts.1.lower,by omega⟩,facts.2.2.1,facts.2.2.2.2,
    complete.heapCell,by have sameNumber:=congrArg BitVec.toNat nextEq; omega⟩

theorem Context.scratch_normal {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {frontier ws bs heap : BitVec 64} {done : List Spec}
    (state : Context source frontier ws bs heap done) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source scratch=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ ∃ next,Context post frontier ws bs next done := by
  obtain ⟨answer,next,complete,buffer⟩:=state.scratch_normal_key value normal
  exact ⟨answer,next,complete⟩

inductive Action where
  | table (spec : Spec)
  | constant (offset : Nat) (word : BitVec 64)

def program : List Action→ProgHOL 64
  | []=>scratch
  | .table spec::rest=>tableStore spec.key spec.cap spec.offset (program rest)
  | .constant offset word::rest=>.seq (.store (field "bs" offset) (.const word)) (program rest)

def completed : List Spec→List Action→List Spec
  | done,[]=>done
  | done,.table spec::rest=>completed (spec::done) rest
  | done,.constant _ _::rest=>completed done rest

def Valid : List Spec→List Action→Prop
  | _,[]=>True
  | done,.table spec::rest=>spec.Valid ∧ (∀ old∈done,spec.offset≠old.offset) ∧ Valid (spec::done) rest
  | done,.constant offset _::rest=>offset≤72 ∧ (∀ old∈done,offset≠old.offset) ∧ Valid done rest

/-- Finite syntax enumeration of the SAME seven real BS table calls and
two real constant stores. It is checked equal to the unchanged suffix. -/
def actions : List Action:=
  [.table ⟨20,256,8⟩,.table ⟨20,256,16⟩,.table ⟨52,256,24⟩,.table ⟨20,64,32⟩,
   .table ⟨52,64,40⟩,.table ⟨32,64,48⟩,.constant 56 0#64,.constant 64 0#64,.table ⟨20,256,72⟩]

def specs : List Spec:=completed [] actions

theorem actions_valid : Valid [] actions := by
  simp [Valid,actions,Spec.Valid]

theorem program_shape : afterBlockAllocation=.seq (.store (field "bs" 0) (.var .global (ofString "ws"))) (program actions) := by
  rw [shape]
  rfl

/-- Actual normal execution advances the initialized-image context through
each original table/field operation, then through scratch and journal setup. -/
theorem actions_normal_key (commands : List Action) : ∀ {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {frontier ws bs heap : BitVec 64} {done : List Spec},
    Context source frontier ws bs heap done→Valid done commands→∀ value,
    evaluateHOLFiniteState source (program commands)=(some (.returned value),post)→
    value=.val (.word 0#64) ∧ ∃ next,Context post frontier ws bs next (completed done commands) ∧ KeyBuffer post bs := by
  induction commands with
  | nil=>
    intro source post frontier ws bs heap done state valid value normal
    exact state.scratch_normal_key value normal
  | cons action rest ih=>
    intro source post frontier ws bs heap done state valid value normal
    cases action with
    | table spec=>
      obtain ⟨specValid,different,tailValid⟩:=valid
      change evaluateHOLFiniteState source (tableStore spec.key spec.cap spec.offset (program rest))=(some (.returned value),post) at normal
      have safe : LocalPrefix (ofString "_") (tableCall spec.key spec.cap):=
        .call (some (ofString "t")) _ _ (by intro name same; cases Option.some.inj same; decide)
      obtain ⟨middle,called,continued,preserved⟩:=safe.normal_continue source post (.seq (.store (field "bs" spec.offset) (localVar "t")) (program rest)) value normal
      have storeSafe : LocalPrefix (ofString "_") (.store (field "bs" spec.offset) (localVar "t")):=.store _ _
      obtain ⟨target,stored,remaining,preserved⟩:=storeSafe.normal_continue middle post (program rest) value continued
      exact ih (state.table spec specValid different called stored) tailValid value remaining
    | constant offset word=>
      obtain ⟨inside,different,tailValid⟩:=valid
      change evaluateHOLFiniteState source (.seq (.store (field "bs" offset) (.const word)) (program rest))=(some (.returned value),post) at normal
      have safe : LocalPrefix (ofString "_") (.store (field "bs" offset) (.const word)):=.store _ _
      obtain ⟨middle,stored,continued,preserved⟩:=safe.normal_continue source post (program rest) value normal
      obtain ⟨current,fieldCell,recordFrame⟩:=state.store offset inside different (.const word) word rfl stored
      exact ih current tailValid value continued

theorem actions_normal (commands : List Action) {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frontier ws bs heap : BitVec 64} {done : List Spec}
    (state : Context source frontier ws bs heap done) (valid : Valid done commands) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (program commands)=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ ∃ next,Context post frontier ws bs next (completed done commands) := by
  obtain ⟨answer,next,complete,buffer⟩:=actions_normal_key commands state valid value normal
  exact ⟨answer,next,complete⟩

/-- Complete real block-state initialization derives all seven empty table
images and pairwise allocation separation below its actual final heap.
There is no future getter/table-image hypothesis at this entry point. -/
theorem after_block_allocation_tables_key {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {frontier ws bs : BitVec 64}
    (physical : MemoryContext source frontier ws bs) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterBlockAllocation=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ ∃ next,Context post frontier ws bs next specs ∧ KeyBuffer post bs := by
  rw [program_shape] at normal
  have safe : LocalPrefix (ofString "_") (.store (field "bs" 0) (.var .global (ofString "ws"))):=.store _ _
  obtain ⟨middle,stored,continued,preserved⟩:=safe.normal_continue source post (program actions) value normal
  have read : eval source (.var .global (ofString "ws"))=some (.val (.word ws)):=by simp [eval,evalHOLExact,physical.wsCell]
  have addressRead : eval source (field "bs" 0)=some (.val (.word bs)):=by
    simpa [eval,field,evalHOLExact,evalListHOLExact,physical.bsCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  obtain ⟨current,frame⟩:=physical.word_store (field "bs" 0) (.var .global (ofString "ws")) bs ws addressRead read physical.bsFresh.1 stored
  obtain ⟨heap,heapCell,owned,bounded,aligned,before⟩:=current.heap
  exact actions_normal_key actions (Context.empty current heapCell) actions_valid value continued

theorem after_block_allocation_tables {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {frontier ws bs : BitVec 64}
    (physical : MemoryContext source frontier ws bs) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterBlockAllocation=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ ∃ next,Context post frontier ws bs next specs := by
  obtain ⟨answer,next,complete,buffer⟩:=after_block_allocation_tables_key physical value normal
  exact ⟨answer,next,complete⟩

end InitECandidate.Solver.Mpt.StateInit.MemorySuffix.BlockTables

#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.BlockTables.Context.finish_normal
#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.BlockTables.Context.journal_normal
#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.BlockTables.Context.scratch_normal
#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.BlockTables.actions_valid
#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.BlockTables.program_shape
#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.BlockTables.actions_normal
#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.BlockTables.after_block_allocation_tables

namespace InitECandidate.Solver.Mpt.StateInit.MemorySuffix.BlockTables
open Input Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Completed actual BS table initialization, separate from the physical
context used while those same tables are still being constructed. -/
def Complete (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frontier ws bs : BitVec 64) : Prop:=
  ∃ heap,Context source frontier ws bs heap specs

theorem Complete.memory {source : PanSemStateFiniteExact 64 Guest.HostMemory} {frontier ws bs : BitVec 64}
    (state : Complete source frontier ws bs) : MemoryContext source frontier ws bs := by
  obtain ⟨heap,current⟩:=state
  exact current.memory

theorem Complete.of_erase {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {frontier ws bs : BitVec 64}
    (state : Complete source frontier ws bs) (same : LocalEffects.erase target=LocalEffects.erase source) : Complete target frontier ws bs := by
  obtain ⟨heap,current⟩:=state
  exact ⟨heap,current.of_erase same⟩

/-- At the actual next allocation frontier, all seven initialized table
extents are below that same word; no new heap value is selected independently. -/
theorem Complete.at_heap {source : PanSemStateFiniteExact 64 Guest.HostMemory} {frontier ws bs heap : BitVec 64}
    (state : Complete source frontier ws bs) (cell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) :
    Images source bs heap specs ∧ Separated source bs specs := by
  obtain ⟨actual,current⟩:=state
  have same : actual=heap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (current.heapCell.symm.trans cell)))
  subst actual
  exact ⟨current.images,current.separated⟩

end InitECandidate.Solver.Mpt.StateInit.MemorySuffix.BlockTables

#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.BlockTables.Complete.memory
#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.BlockTables.Complete.of_erase
#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.BlockTables.Complete.at_heap


#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.BlockTables.journal_key_buffer_global
#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.BlockTables.KeyBuffer.of_erase
#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.BlockTables.Context.journal_normal_grows
#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.BlockTables.Context.scratch_normal_key

#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.BlockTables.actions_normal_key
#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.BlockTables.after_block_allocation_tables_key
