import InitECandidate.Solver.Input.Requests.SetupProgram
import InitECandidate.Solver.Input.RequestLoad

namespace InitECandidate.Solver.Input.Requests
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch ProgramPrefix

/-- Original80-byte request allocation and all five actual offset loads.
No request-list success is supplied. The workspace values are those already
written/validated by the real prefix, and input memory remains unchanged. -/
theorem setup (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer array cursor : BitVec 64) (start : Nat)
    (heap : Blob.HeapInput source input pointer)
    (offsets : source.globals.lookup (ofString "ssz_offs") = some (.val (.word array)))
    (cells : ∀ position < 5,source.memory (byteAddress array (8*position)) = .word (offsetWord input start position))
    (domain : source.memaddrs = InitE.ordinaryDomain) (arrayAligned : array.toNat % 8 = 0)
    (arrayArena : Arena array 40)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word cursor)))
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals,PersistentAlloc.body,.one))
    (room : cursor.toNat + 80 ≤ 33806089496) (enough : 1 ≤ source.clock) :
    Executes source setupActions (prepared source input cursor start) (restoreSetup source input cursor start) ∧
      Blob.HeapInput (prepared source input cursor start) input pointer := by
  have global : (allocated source cursor).globals.lookup (ofString "ssz_offs") = some (.val (.word array)) := by
    change (source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded cursor 80#64)))).lookup (ofString "ssz_offs") = _
    simpa [HolFiniteMapExact.lookup_update,FUPDATE,show (ofString "heap_ptr" == ofString "ssz_offs") = false from by decide] using offsets
  have read (current : PanSemStateFiniteExact 64 Guest.HostMemory) (position : Nat) (small : position < 5)
      (currentGlobal : current.globals.lookup (ofString "ssz_offs") = some (.val (.word array)))
      (memory : current.memory = source.memory) (addresses : current.memaddrs = source.memaddrs) :
      eval current (loadOffset position) = some (.val (.word (offsetWord input start position))) := by
    have mapped := word_mapped current array 40 (8*position) (addresses.trans domain) arrayArena (by omega) arrayAligned (by omega)
    have cell : current.memory (array + BitVec.ofNat 64 (8*position)) = .word (offsetWord input start position) := by rw [memory]; exact cells position small
    by_cases zero : position = 0
    · subst position
      have mappedZero : current.memaddrs array := by simpa [byteAddress] using mapped
      have cellZero : current.memory array = .word (offsetWord input start 0) := by simpa using cell
      simp [loadOffset,eval,Header.offsets,evalHOLExact,toExact,currentGlobal,isWfShapeExactHOL,memLoadHOLExact,mappedZero,cellZero]
    · rw [loadOffset,if_neg zero]
      exact Request.word_read current array (offsetWord input start position) (8*position) currentGlobal mapped cell
  have r0 := read (allocated source cursor) 0 (by decide) global rfl rfl
  have r1 := read (loaded0 source input cursor start) 1 (by decide) global rfl rfl
  have r2 := read (loaded1 source input cursor start) 2 (by decide) global rfl rfl
  have r3 := read (loaded2 source input cursor start) 3 (by decide) global rfl rfl
  have r4 := read (loaded3 source input cursor start) 4 (by decide) global rfl rfl
  refine ⟨?_,Blob.HeapInput.of_fields source (prepared source input cursor start) input pointer rfl rfl rfl heap⟩
  exact .allocate cursor 80#64 rfl allocCode heapGlobal room enough
    (.declare (offsetWord input start 0) r0 (.declare (offsetWord input start 1) r1
      (.declare (offsetWord input start 2) r2 (.declare (offsetWord input start 3) r3
        (.declare (offsetWord input start 4) r4 (.done _))))))

end InitECandidate.Solver.Input.Requests

#print axioms InitECandidate.Solver.Input.Requests.setup
