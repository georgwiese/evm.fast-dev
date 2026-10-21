import InitECandidate.Solver.Input.RootBoundaryMemoryFrame
import InitECandidate.Solver.Rlp.ValidationWriteFrame

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- A real helper's restored heap and scratch-memory frame preserve both
constructed databases. Only the present cursor's physical upper bound is
needed; no temporary allocation success or future execution is assumed. -/
theorem RootBoundary.scratch_frame (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (cursor : BitVec 64) (actual : RootBoundary input source) (below : cursor.toNat≤2713717616)
    (heap : target.globals.lookup (ofString "heap_ptr")=source.globals.lookup (ofString "heap_ptr"))
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (db : target.locals.lookup (ofString "db")=source.locals.lookup (ofString "db"))
    (memory : Rlp.Validation.Above source target cursor.toNat) : RootBoundary input target := by
  have originalBoundary:=actual
  obtain ⟨codeArray,nodes,codes,frontier,nodeDatabase,codeDatabase,nodeCell,heapCell,arena,aligned,nodeBefore,codeBefore⟩:=actual
  exact originalBoundary.memory_frame input source target frontier frontier heapCell (heap.trans heapCell) arena aligned (Nat.le_refl _)
    domain.symm endian.symm db (fun query lower upper=>memory query (below.trans lower))

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.RootBoundary.scratch_frame
