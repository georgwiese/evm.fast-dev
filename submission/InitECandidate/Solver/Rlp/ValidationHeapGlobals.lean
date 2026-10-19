import InitECandidate.Solver.Rlp.ValidationArena
import InitECandidate.Solver.PanHeapGlobals

namespace InitECandidate.Solver.Rlp.Validation
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Heap-only global effects retain the current scratch arena, even while
the persistent cursor and unrelated ordinary memory change. -/
theorem Arena.of_heap_globals (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor limit : BitVec 64)
    (arena : Arena source cursor limit) (domain : target.memaddrs=source.memaddrs) (globals : HeapGlobals source target) : Arena target cursor limit :=
  ⟨domain.trans arena.domain,(globals _ (by decide)).trans arena.cursorGlobal,(globals _ (by decide)).trans arena.limitGlobal,
    arena.ordered,arena.aligned,arena.lower,arena.upper⟩

end InitECandidate.Solver.Rlp.Validation

#print axioms InitECandidate.Solver.Rlp.Validation.Arena.of_heap_globals
