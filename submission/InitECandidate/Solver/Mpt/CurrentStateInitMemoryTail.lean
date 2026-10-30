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
  obtain ⟨heap,heapCell,heapArena,heapBound,heapAligned,before⟩:=context.heap
  obtain ⟨tableCell,otherLocals,tableArena,physical⟩:=CurrentTable.New.scalar_local_normal_frame source middle "t"
    (BitVec.ofNat 64 key) (BitVec.ofNat 64 cap) heap [.const (BitVec.ofNat 64 key),.const (BitVec.ofNat 64 cap)] rfl capLower
    heapCell heapArena heapBound heapAligned context.arena firstRun
  have current:=context.after_persistent physical before heapCell
  have first:=physical.memory_frame.weaken source middle heap frontier before
  have tableRead : eval middle (localVar "t")=some (.val (.word heap)):=by simp [eval,evalHOLExact,localVar,toExact,tableCell]
  obtain ⟨valueEq,finalArena,last⟩:=store_suffix_normal middle post frontier ws bs current offset inside (localVar "t") heap tableRead continuation tail value continued
  exact ⟨valueEq,finalArena,first.trans source middle post frontier frontier last (Nat.le_refl _)⟩

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
  have first : PersistentMemoryFrame source middle frontier:=by
    rw [endpoint]
    exact PersistentMemoryFrame.put_global source source frontier ⟨context.heap,rfl,by intros; rfl⟩ "journal_cap" 524288#64 (by decide)
  have capCell : middle.globals.lookup (ofString "journal_cap")=some (.val (.word 524288#64)):=by
    rw [endpoint]
    exact putGlobal.lookup_same _ _ _
  have args : evalListHOLFinite middle (h:=fun query=>Classical.propDecidable (middle.memaddrs query))
      [.panop .mul [.var .global (ofString "journal_cap"),.const 32#64]]=some (PersistentAlloc.values 16777216#64) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,capCell,valueIsWord,valueWord,panOpHOL,PersistentAlloc.values]
  obtain ⟨valueEq,finalArena,last⟩:=allocate_suffix_normal middle post frontier ws bs current "journal" 16777216#64 _ finish args
    (by decide) (by decide) (by decide) (by decide) (by decide) (finish_frame frontier ws bs) value continued
  exact ⟨valueEq,finalArena,first.trans source middle post frontier frontier last (Nat.le_refl _)⟩

theorem scratch_frame (frontier ws bs : BitVec 64) : Tail frontier ws bs scratch := by
  intro source post context value normal
  exact allocate_suffix_normal source post frontier ws bs context "sk_buf" 64#64 [.const 64#64] journal rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (journal_frame frontier ws bs) value normal

/-- Every actual normal block-state suffix preserves the original earlier
input and complete runtime metadata while initializing its real tables,
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
