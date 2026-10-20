import InitECandidate.Solver.Input.Requests.SetupTrace
import InitECandidate.Solver.Input.Requests.SetupFields

namespace InitECandidate.Solver.Input.Requests
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Actual request setup with only the reached state and post-frame exposed. -/
theorem setup_reached (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer array cursor : BitVec 64) (start : Nat)
    (heap : Blob.HeapInput source input pointer)
    (offsets : source.globals.lookup (ofString "ssz_offs") = some (.val (.word array)))
    (cells : ∀ position < 5,source.memory (byteAddress array (8*position)) = .word (offsetWord input start position))
    (domain : source.memaddrs = InitE.ordinaryDomain) (arrayAligned : array.toNat % 8 = 0) (arrayArena : Arena array 40)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word cursor)))
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals,PersistentAlloc.body,.one))
    (room : cursor.toNat + 80 ≤ 33806089496)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterOffsets = (result,post)) (notTimeout : result ≠ some .timeOut) :
    1 ≤ source.clock ∧ ∃ innerPost,Blob.HeapInput (prepared source input cursor start) input pointer ∧
      evaluateHOLFiniteState (prepared source input cursor start) countCalls = (result,innerPost) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite innerPost := by
  obtain ⟨funded,innerPost,setup,bytes,remaining,restored⟩ := setup_trace source post input pointer array cursor start heap offsets cells domain arrayAligned arrayArena heapGlobal allocCode room result run notTimeout
  have frame : emptyLocalsHOLFinite post = emptyLocalsHOLFinite innerPost := by
    rw [restored]
    exact restore_setup_frame source innerPost input cursor start
  exact ⟨funded,innerPost,bytes,remaining,frame⟩

end InitECandidate.Solver.Input.Requests

#print axioms InitECandidate.Solver.Input.Requests.setup_reached
