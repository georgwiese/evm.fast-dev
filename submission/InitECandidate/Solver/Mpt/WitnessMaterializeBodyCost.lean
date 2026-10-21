import InitECandidate.Solver.Mpt.WitnessCoreBodyCost
import InitECandidate.Solver.Mpt.WitnessCoreEntryTrace

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Whole original witness materializer, including both actual wrapper
calls, scratch-mark handling and normal/exceptional continuations. The
original core bound is instantiated at the genuine preserved callee entry. -/
theorem materialize_body_cost (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap cursor limit : BitVec 64) (boundary : RootBoundary input source)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapLower : 2713731432≤heap.toNat)
    (arena : Rlp.Validation.Arena source cursor limit) (below : cursor.toNat≤2713717616)
    (before : pointer.toNat+length.toNat≤db.toNat) (small : length.toNat≤1024) (lower : 2713731432≤pointer.toNat)
    (installed : OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source Mpt.WitnessMaterialize.body).2.clock≤(Mpt.WitnessCore.Stack.iterationCost input+1)*6864962+6 := by
  let output:=evaluateHOLFiniteState source Mpt.WitnessMaterialize.body
  rcases Mpt.WitnessMaterialize.core_trace source output.2 db pointer length cursor installed dbCell pointerCell lengthCell arena.cursorGlobal output.1 rfl with stopped|entered
  · exact stopped.trans (by omega)
  · obtain ⟨entry,target,result,pure,clock,entryDb,entryPointer,entryLength,run,paid⟩:=entered
    have entryBoundary:=boundary.erase_frame input source entry pure (entryDb.trans dbCell.symm)
    have globals:=congrArg PanSemStateFiniteExact.globals pure
    change entry.globals=source.globals at globals
    have domain:=congrArg PanSemStateFiniteExact.memaddrs pure
    change entry.memaddrs=source.memaddrs at domain
    have entryHeap : entry.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by rw [globals]; exact heapCell
    have entryArena:=arena.of_fields source entry cursor limit domain globals
    have entryInstalled : OriginalCode.Installed entry.code:=by rw [LocalEffects.code_of_erase source entry pure]; exact installed
    have corePaid:=Mpt.WitnessCore.Stack.body_cost input entry db pointer length heap cursor limit entryBoundary entryDb entryPointer entryLength entryHeap heapLower entryArena below before small lower entryInstalled
    rw [run] at corePaid
    change entry.clock-target.clock≤(Mpt.WitnessCore.Stack.iterationCost input+1)*6864962 at corePaid
    change source.clock-output.2.clock≤(Mpt.WitnessCore.Stack.iterationCost input+1)*6864962+6
    omega

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.materialize_body_cost
