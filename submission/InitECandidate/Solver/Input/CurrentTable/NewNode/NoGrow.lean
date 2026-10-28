import InitECandidate.Solver.Input.CurrentTable.NewNode.Program

namespace InitECandidate.Solver.Input.CurrentTable.NewNode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open Flapjack.Compiler.Encoders.Asm

def freeEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) := bind source "f" 0#64
def nextEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (next : BitVec 64) := bind (freeEntry source) "next" next
def nodeEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (next : BitVec 64) := bind (nextEntry source next) "n" next

def returnedState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table next : BitVec 64) :=
  restore source "f" (restore (freeEntry source) "next" (restore (nextEntry source next) "n"
    (emptyLocalsHOLFinite (New.putField (nodeEntry source next) table 64 (next+1#64)))))

theorem free_guard_skip (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (cell : source.locals.lookup (ofString "f") = some (.val (.word 0#64))) :
    evaluateHOLFiniteState source freeGuard = (none,source) := by
  rw [freeGuard,evaluateHOLFiniteState_ite]
  simp [evalHOLExact,localVar,cell,wordCmpHOL,evaluateHOLFiniteState_skip]

theorem grow_guard_skip (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table next cap : BitVec 64)
    (domain : source.memaddrs = InitE.ordinaryDomain) (arena : AllocatedBytes.Arena table 88)
    (aligned : table.toNat%8 = 0)
    (tableCell : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (nextCell : source.locals.lookup (ofString "next") = some (.val (.word next)))
    (capCell : source.memory (table+80#64) = .word cap) (room : next.toNat ≤ cap.toNat) :
    evaluateHOLFiniteState source growGuard = (none,source) := by
  have capRead := field_read source table cap 80 domain arena aligned (by decide) (by decide) tableCell capCell
  have read : eval source (.cmp .lower (.load .one (address 80)) (localVar "next")) = some (.val (.word 0#64)) := by
    simp only [eval] at capRead ⊢
    rw [evalHOLExact]
    simp only [capRead]
    simp [evalHOLExact,localVar,nextCell,wordCmpHOL,BitVec.lt_def,show ¬cap.toNat < next.toNat from by omega]
  rw [growGuard,evaluateHOLFiniteState_ite]
  simp only [eval] at read
  rw [read]
  simp [evaluateHOLFiniteState_skip]

/-- The no-grow allocator tail stores the real increment and returns its
actual previous next-node index, at every source clock including zero. -/
theorem after_node_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table next : BitVec 64)
    (domain : source.memaddrs = InitE.ordinaryDomain) (arena : AllocatedBytes.Arena table 88)
    (aligned : table.toNat%8 = 0)
    (tableCell : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (nodeCell : source.locals.lookup (ofString "n") = some (.val (.word next))) :
    evaluateHOLFiniteState source afterNode =
      (some (.returned (.val (.word next))),emptyLocalsHOLFinite (New.putField source table 64 (next+1#64))) := by
  have valueRead : eval source (.op .add [localVar "n",.const 1#64]) = some (.val (.word (next+1#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,nodeCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have store := New.store_field source table (next+1#64) 64 _ domain arena aligned (by decide) (by decide) tableCell valueRead
  change evaluateHOLFiniteState source (.store (address 64) (.op .add [localVar "n",.const 1#64])) = _ at store
  rw [shapes.2.2.2.2.2,evaluateHOLFiniteState_seq_line780,store]
  simp [evaluateHOLFiniteState_return,evalHOLExact,localVar,New.putField,nodeCell,shapeOfHOLExact,sizeOfShapeWithContextHOL]

/-- With the real empty free-list and available node index, the unchanged
allocator follows no recursive/grow call. It spends no body source ticks
and changes only the next-index metadata word. -/
theorem body_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table next cap : BitVec 64)
    (domain : source.memaddrs = InitE.ordinaryDomain) (arena : AllocatedBytes.Arena table 88)
    (aligned : table.toNat%8 = 0)
    (tableCell : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (freeCell : source.memory (table+72#64) = .word 0#64)
    (nextCell : source.memory (table+64#64) = .word next)
    (capCell : source.memory (table+80#64) = .word cap) (room : next.toNat ≤ cap.toNat) :
    evaluateHOLFiniteState source body = (some (.returned (.val (.word next))),returnedState source table next) := by
  have freeRead := field_read source table 0#64 72 domain arena aligned (by decide) (by decide) tableCell freeCell
  have firstTable : (freeEntry source).locals.lookup (ofString "t") = some (.val (.word table)) :=
    (bind_lookup_other source "f" "t" 0#64 (by decide)).trans tableCell
  have nextRead := field_read (freeEntry source) table next 64 domain arena aligned (by decide) (by decide) firstTable nextCell
  have secondTable : (nextEntry source next).locals.lookup (ofString "t") = some (.val (.word table)) :=
    (bind_lookup_other (freeEntry source) "next" "t" next (by decide)).trans firstTable
  have lastRead := field_read (nextEntry source next) table next 64 domain arena aligned (by decide) (by decide) secondTable nextCell
  have lastTable : (nodeEntry source next).locals.lookup (ofString "t") = some (.val (.word table)) :=
    (bind_lookup_other (nextEntry source next) "n" "t" next (by decide)).trans secondTable
  have tail := after_node_execute (nodeEntry source next) table next domain arena aligned lastTable (bind_lookup_same _ _ _)
  have last : evaluateHOLFiniteState (nextEntry source next) afterGrow =
      (some (.returned (.val (.word next))),restore (nextEntry source next) "n"
        (emptyLocalsHOLFinite (New.putField (nodeEntry source next) table 64 (next+1#64)))) := by
    rw [shapes.2.2.2.2.1]
    exact ScalarScope.declare_execute _ _ "n" _ next afterNode _ lastRead tail
  have grown : evaluateHOLFiniteState (nextEntry source next) afterNext = evaluateHOLFiniteState (nextEntry source next) afterGrow := by
    rw [shapes.2.2.2.1,evaluateHOLFiniteState_seq_line780,
      grow_guard_skip (nextEntry source next) table next cap domain arena aligned secondTable (bind_lookup_same _ _ _) capCell room]
  have middle : evaluateHOLFiniteState (freeEntry source) afterFreeGuard =
      (some (.returned (.val (.word next))),restore (freeEntry source) "next"
        (restore (nextEntry source next) "n" (emptyLocalsHOLFinite (New.putField (nodeEntry source next) table 64 (next+1#64))))) := by
    rw [shapes.2.2.1]
    apply ScalarScope.declare_execute _ _ "next" _ next afterNext _ nextRead
    change evaluateHOLFiniteState (nextEntry source next) afterNext = _
    rw [grown,last]
  have skipped : evaluateHOLFiniteState (freeEntry source) afterFree = evaluateHOLFiniteState (freeEntry source) afterFreeGuard := by
    rw [shapes.2.1,evaluateHOLFiniteState_seq_line780,free_guard_skip (freeEntry source) (bind_lookup_same _ _ _)]
  rw [shapes.1]
  apply ScalarScope.declare_execute source _ "f" _ 0#64 afterFree _ freeRead
  change evaluateHOLFiniteState (freeEntry source) afterFree = _
  rw [skipped,middle]

theorem returned_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table next : BitVec 64) :
    LocalEffects.erase (returnedState source table next) = LocalEffects.erase (New.putField source table 64 (next+1#64)) ∧
      (returnedState source table next).clock = source.clock := ⟨rfl,rfl⟩

end InitECandidate.Solver.Input.CurrentTable.NewNode

#print axioms InitECandidate.Solver.Input.CurrentTable.NewNode.grow_guard_skip
#print axioms InitECandidate.Solver.Input.CurrentTable.NewNode.body_execute
#print axioms InitECandidate.Solver.Input.CurrentTable.NewNode.returned_frame
