import InitECandidate.Solver.Mpt.CurrentWitnessCoreLoop
import InitECandidate.Solver.Mpt.WitnessCoreInitial
import InitECandidate.Solver.Input.ClockCostCurrent

namespace InitECandidate.Solver.Mpt.WitnessCore
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The genuine seven initial declarations derive the small reachable
loop state while retaining the current physical arena and allocator. -/
theorem current_initial_entry (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap : BitVec 64)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (arena : CurrentStartup.ArenaState source) :
    CurrentDecodeEntry (ready source pointer length) db pointer length heap := by
  have cells:=ready_fields source pointer length
  exact ⟨arena.of_frame rfl,heapCell,(ready_other source pointer length (ofString "db") (by decide)).trans dbCell,
    cells.2.2.1,cells.2.2.2.1,cells.2.1,cells.2.2.2.2.1,cells.1,cells.2.2.2.2.2.2⟩

/-- Whole unchanged current236, including all initial scopes, both
reachable loop iterations and the real result footer. No future normal return
or recursive traversal is an entry assumption. -/
theorem current_body_price (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap : BitVec 64)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (small : length.toNat≤1024) (before : pointer.toNat+length.toNat≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤length.toNat/4+195*length.toNat+287 := by
  have entry:=current_initial_entry source db pointer length heap dbCell heapCell arena
  have loopPrice:=current_loop_price (ready source pointer length) db pointer length heap entry small before heapArena heapBound aligned
  have suffixPrice:=ClockCost.sequence_current (ready source pointer length) (.while condition loopBody) footer _ 0 loopPrice
    (ClockCost.returned _ (localVar "result"))
  let output:=evaluateHOLFiniteState source body
  obtain ⟨restoreStack,inner,setup,continued,endpoint,clock⟩:=initial_trace source output.2 pointer length pointerCell lengthCell output.1 rfl
  rw [continued] at suffixPrice
  change source.clock-inner.clock≤length.toNat/4+195*length.toNat+287+0 at suffixPrice
  change source.clock-output.2.clock≤length.toNat/4+195*length.toNat+287
  rw [clock]
  exact Nat.le_trans suffixPrice (by omega)

theorem current_body_literal_price (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap : BitVec 64)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (small : length.toNat≤1024) (before : pointer.toNat+length.toNat≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤200223 :=
  Nat.le_trans (current_body_price source db pointer length heap dbCell pointerCell lengthCell small before heapCell heapArena heapBound aligned arena) (by omega)

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.current_initial_entry
#print axioms InitECandidate.Solver.Mpt.WitnessCore.current_body_price
#print axioms InitECandidate.Solver.Mpt.WitnessCore.current_body_literal_price
