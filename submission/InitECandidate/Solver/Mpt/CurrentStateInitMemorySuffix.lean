import InitECandidate.Solver.Mpt.CurrentStateInitMemoryContext
import InitECandidate.Solver.Mpt.StateInitProgram
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.Input.ReturnNormal

namespace InitECandidate.Solver.Mpt.StateInit.MemorySuffix
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def field (name : String) (offset : Nat) : ExpHOL 64:=.op .add [.var .global (ofString name),.const (BitVec.ofNat 64 offset)]
def tableCall (key cap : Nat) : ProgHOL 64:=.call (some (some (.local,ofString "t"),none)) (ofString "htab_new") [.const (BitVec.ofNat 64 key),.const (BitVec.ofNat 64 cap)]
def tableStore (key cap offset : Nat) (tail : ProgHOL 64) : ProgHOL 64:=.seq (tableCall key cap) (.seq (.store (field "bs" offset) (localVar "t")) tail)
def allocate (name : String) (arguments : List (ExpHOL 64)) : ProgHOL 64:=.call (some (some (.global,ofString name),none)) (ofString "alloc") arguments
def finish : ProgHOL 64:=.seq (.assign .global (ofString "journal_n") (.const 0#64)) (.seq (.assign .global (ofString "ts") (.const 0#64)) (.return (.const 0#64)))
def journal : ProgHOL 64:=.seq (.assign .global (ofString "journal_cap") (.const 524288#64))
  (.seq (allocate "journal" [.panop .mul [.var .global (ofString "journal_cap"),.const 32#64]]) finish)
def scratch : ProgHOL 64:=.seq (allocate "sk_buf" [.const 64#64]) journal

def afterTable : ProgHOL 64:=match afterRoot with | .seq _ (.decCall _ _ _ _ rest)=>rest | _=>.skip
def afterBlockAllocation : ProgHOL 64:=match afterTable with | .seq _ (.seq _ rest)=>rest | _=>.skip

set_option maxRecDepth 100000 in
/-- The actual block-state suffix, retaining all seven real table calls,
its metadata stores and the remaining scratch/journal initializations. -/
theorem shape : afterBlockAllocation=.seq (.store (field "bs" 0) (.var .global (ofString "ws")))
    (tableStore 20 256 8 (tableStore 20 256 16 (tableStore 52 256 24 (tableStore 20 64 32 (tableStore 52 64 40 (tableStore 32 64 48
      (.seq (.store (field "bs" 56) (.const 0#64)) (.seq (.store (field "bs" 64) (.const 0#64)) (tableStore 20 256 72 scratch))))))))) := by
  simp only [afterBlockAllocation,afterTable,afterRoot,rootCall,afterSecond,afterFirst,afterAllocation,body,
    Guest.Software.guestFn_state_init,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,
    tableStore,tableCall,field,scratch,journal,finish,allocate,localVar]

/-- Actual normal block-state tails retain their real heap and all input
before the original entering frontier. -/
def Tail (frontier ws bs : BitVec 64) (program : ProgHOL 64) : Prop:=
  ∀ source post,MemoryContext source frontier ws bs → ∀ value,
    evaluateHOLFiniteState source program=(some (.returned value),post) →
    value=.val (.word 0#64) ∧ CurrentStartup.ArenaState post ∧ PersistentMemoryFrame source post frontier

theorem Tail.returned (frontier ws bs : BitVec 64) : Tail frontier ws bs (.return (.const 0#64)) := by
  intro source post context value normal
  obtain ⟨read,endpoint⟩:=return_normal source post (.const 0#64) value normal
  have first : PersistentMemoryFrame source source frontier:=⟨context.heap,rfl,by intros; rfl⟩
  exact ⟨Option.some.inj read.symm,(by rw [endpoint]; exact context.arena.of_frame rfl),first.of_erase source source source post frontier rfl (by rw [endpoint]; rfl)⟩

theorem Tail.global_constant (frontier ws bs : BitVec 64) (name : String) (word : BitVec 64) (continuation : ProgHOL 64)
    (notHeap : ofString "heap_ptr"≠ofString name) (notWs : ofString "ws"≠ofString name) (notBs : ofString "bs"≠ofString name)
    (notScratch : ofString "scratch_ptr"≠ofString name) (notFrame : ofString "frame_mem_ptr"≠ofString name)
    (tail : Tail frontier ws bs continuation) : Tail frontier ws bs (.seq (.assign .global (ofString name) (.const word)) continuation) := by
  intro source post context value normal
  have safe : LocalPrefix (ofString "_") (.assign .global (ofString name) (.const word)):=.globalAssign _ _
  obtain ⟨middle,firstRun,continued,preserved⟩:=safe.normal_continue source post continuation value normal
  have endpoint:=global_assign_none source middle name (.const word) word rfl firstRun
  have current : MemoryContext middle frontier ws bs:=by rw [endpoint]; exact context.put_global name word notHeap notWs notBs notScratch notFrame
  have first : PersistentMemoryFrame source middle frontier:=by
    rw [endpoint]
    exact (PersistentMemoryFrame.put_global source source frontier ⟨context.heap,rfl,by intros; rfl⟩ name word notHeap)
  obtain ⟨valueEq,finalArena,last⟩:=tail middle post current value continued
  exact ⟨valueEq,finalArena,first.trans source middle post frontier frontier last (Nat.le_refl _)⟩

theorem allocate_suffix_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frontier ws bs : BitVec 64)
    (context : MemoryContext source frontier ws bs) (name : String) (amount : BitVec 64) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (PersistentAlloc.values amount))
    (notHeap : ofString "heap_ptr"≠ofString name) (notWs : ofString "ws"≠ofString name) (notBs : ofString "bs"≠ofString name)
    (notScratch : ofString "scratch_ptr"≠ofString name) (notFrame : ofString "frame_mem_ptr"≠ofString name)
    (tail : Tail frontier ws bs continuation) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.seq (allocate name arguments) continuation)=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ CurrentStartup.ArenaState post ∧ PersistentMemoryFrame source post frontier := by
  have safe : LocalPrefix (ofString "_") (allocate name arguments):=.globalCall _ _ _
  obtain ⟨middle,firstRun,continued,preserved⟩:=safe.normal_continue source post continuation value normal
  obtain ⟨current,first⟩:=context.allocate_global name amount arguments args notHeap notWs notBs notScratch notFrame firstRun
  obtain ⟨valueEq,finalArena,last⟩:=tail middle post current value continued
  exact ⟨valueEq,finalArena,first.trans source middle post frontier frontier last (Nat.le_refl _)⟩

theorem store_suffix_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frontier ws bs : BitVec 64)
    (context : MemoryContext source frontier ws bs) (offset : Nat) (inside : offset≤72) (expression : ExpHOL 64) (word : BitVec 64)
    (read : eval source expression=some (.val (.word word))) (continuation : ProgHOL 64) (tail : Tail frontier ws bs continuation) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.seq (.store (field "bs" offset) expression) continuation)=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ CurrentStartup.ArenaState post ∧ PersistentMemoryFrame source post frontier := by
  have safe : LocalPrefix (ofString "_") (.store (field "bs" offset) expression):=.store _ _
  obtain ⟨middle,firstRun,continued,preserved⟩:=safe.normal_continue source post continuation value normal
  have addressRead : eval source (field "bs" offset)=some (.val (.word (bs+BitVec.ofNat 64 offset))) := by
    simp [eval,field,evalHOLExact,evalListHOLExact,context.bsCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have number:=byteAddress_toNat bs offset (by have upper:=context.bsFresh.2; omega)
  change (bs+BitVec.ofNat 64 offset).toNat=bs.toNat+offset at number
  obtain ⟨current,first⟩:=context.word_store (field "bs" offset) expression _ word addressRead read (by rw [number]; have lower:=context.bsFresh.1; omega) firstRun
  obtain ⟨valueEq,finalArena,last⟩:=tail middle post current value continued
  exact ⟨valueEq,finalArena,first.trans source middle post frontier frontier last (Nat.le_refl _)⟩

end InitECandidate.Solver.Mpt.StateInit.MemorySuffix

#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.shape
#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.Tail.returned
#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.Tail.global_constant
#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.allocate_suffix_normal
#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.store_suffix_normal
