import InitECandidate.Solver.Input.PayloadRemainingProgram

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem payload_scalar (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer : BitVec 64)
    (heap : Blob.HeapInput source input pointer) (offset : Nat) (inside : 62+offset+8≤input.length%2^64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (pointer+62#64)))) :
    eval source (Scalar.flat64 (localVar "p") [offset])=some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le64 input (62+offset))))) := by
  exact Scalar.flat_heap_le64 source input pointer (pointer+62#64) (localVar "p") [offset] (62+offset) heap inside
    (Request.local_word source "p" _ p) (by simp [BitVec.ofNat_add,BitVec.add_assoc])

theorem remaining_reads (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer length withdrawals balances count : BitVec 64) (heap : Blob.HeapInput source input pointer) (inside : 602≤input.length%2^64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (pointer+62#64))))
    (n : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (w : source.locals.lookup (ofString "o_wd")=some (.val (.word withdrawals)))
    (b : source.locals.lookup (ofString "o_bal")=some (.val (.word balances)))
    (c : source.locals.lookup (ofString "nwd")=some (.val (.word count))) :
    ∀ field∈remainingFields input pointer length withdrawals balances count,eval source field.2.1=some (.val (.word field.2.2)) := by
  intro field mem
  simp only [remainingFields,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · simp [eval,localVar,evalHOLExact,evalListHOLExact,toExact,p,w,valueIsWord,valueWord,wordOpHOL,wordOp]
  · exact Request.local_word source "nwd" count c
  · simp [eval,localVar,evalHOLExact,evalListHOLExact,toExact,p,b,valueIsWord,valueWord,wordOpHOL,wordOp]
  · simp [eval,localVar,evalHOLExact,evalListHOLExact,toExact,n,b,valueIsWord,valueWord,wordOpHOL,wordOp]
  · exact payload_scalar source input pointer heap 404 (by omega) p
  · exact payload_scalar source input pointer heap 412 (by omega) p
  · exact payload_scalar source input pointer heap 420 (by omega) p
  · exact payload_scalar source input pointer heap 428 (by omega) p
  · exact payload_scalar source input pointer heap 512 (by omega) p
  · exact payload_scalar source input pointer heap 520 (by omega) p
  · exact payload_scalar source input pointer heap 532 (by omega) p

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.payload_scalar
#print axioms InitECandidate.Solver.Input.Payload.remaining_reads
