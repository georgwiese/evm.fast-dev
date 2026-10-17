import InitECandidate.Solver.Input.PayloadHeaderStores

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix.ProgramPrefix

def offsetDeclarations : List Action := [
  .declare "o_extra" (Scalar.flat32 (localVar "p") [436]),
  .declare "o_txs" (Scalar.flat32 (localVar "p") [504]),
  .declare "o_wd" (Scalar.flat32 (localVar "p") [508]),
  .declare "o_bal" (Scalar.flat32 (localVar "p") [528])]

def extraState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) :=
  bind (source) "o_extra" (offsetWords input 0)

def txState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) :=
  bind (extraState source input) "o_txs" (offsetWords input 1)

def wdState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) :=
  bind (txState source input) "o_wd" (offsetWords input 2)

def declaredState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) :=
  bind (wdState source input) "o_bal" (offsetWords input 3)

def restoreDeclarations (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (target : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  restore source "o_extra" (restore (extraState source input) "o_txs"
    (restore (txState source input) "o_wd" (restore (wdState source input) "o_bal" target)))

theorem payload_offset_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer : BitVec 64) (extras : List Nat) (start : Nat)
    (heap : Blob.HeapInput source input pointer) (inside : start+4≤input.length%2^64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (pointer+62#64)))) (offset : 62+extras.sum=start) :
    eval source (Scalar.flat32 (localVar "p") extras)=some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le32 input start)))) := by
  have field : pointer+62#64+BitVec.ofNat 64 extras.sum=pointer+BitVec.ofNat 64 start := by
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact congrArg (fun n=>pointer+BitVec.ofNat 64 n) offset
  exact Scalar.flat_heap_le32 source input pointer (pointer+62#64) (localVar "p") extras start heap inside
    (Request.local_word source "p" (pointer+62#64) p) field

/-- All four actual payload offset declarations, preserving copied bytes and
retaining every lexical restoration. Their input bounds follow from extent602. -/
theorem offset_declarations (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer : BitVec 64)
    (heap : Blob.HeapInput source input pointer) (inside : 602≤input.length%2^64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (pointer+62#64)))) :
    Executes source offsetDeclarations (declaredState source input) (restoreDeclarations source input) ∧
    Blob.HeapInput (declaredState source input) input pointer := by
  have r0:=payload_offset_read (source) input pointer [436] 498 heap (by omega) p rfl
  have h1 : Blob.HeapInput (extraState source input) input pointer :=
    Blob.HeapInput.of_fields source (extraState source input) input pointer rfl rfl rfl heap
  have p1 : (extraState source input).locals.lookup (ofString "p")=some (.val (.word (pointer+62#64))) :=
    (bind_lookup_other (source) "o_extra" "p" _ (by decide)).trans p
  have r1:=payload_offset_read (extraState source input) input pointer [504] 566 h1 (by omega) p1 rfl
  have h2 : Blob.HeapInput (txState source input) input pointer :=
    Blob.HeapInput.of_fields source (txState source input) input pointer rfl rfl rfl heap
  have p2 : (txState source input).locals.lookup (ofString "p")=some (.val (.word (pointer+62#64))) :=
    (bind_lookup_other (extraState source input) "o_txs" "p" _ (by decide)).trans p1
  have r2:=payload_offset_read (txState source input) input pointer [508] 570 h2 (by omega) p2 rfl
  have h3 : Blob.HeapInput (wdState source input) input pointer :=
    Blob.HeapInput.of_fields source (wdState source input) input pointer rfl rfl rfl heap
  have p3 : (wdState source input).locals.lookup (ofString "p")=some (.val (.word (pointer+62#64))) :=
    (bind_lookup_other (txState source input) "o_wd" "p" _ (by decide)).trans p2
  have r3:=payload_offset_read (wdState source input) input pointer [528] 590 h3 (by omega) p3 rfl
  refine ⟨?_,Blob.HeapInput.of_fields source (declaredState source input) input pointer rfl rfl rfl heap⟩
  unfold offsetDeclarations restoreDeclarations
  refine Executes.declare (restoreRest:=fun target=>restore (extraState source input) "o_txs" (restore (txState source input) "o_wd" (restore (wdState source input) "o_bal" (target)))) (offsetWords input 0) r0 ?_
  refine Executes.declare (restoreRest:=fun target=>restore (txState source input) "o_wd" (restore (wdState source input) "o_bal" (target))) (offsetWords input 1) r1 ?_
  refine Executes.declare (restoreRest:=fun target=>restore (wdState source input) "o_bal" (target)) (offsetWords input 2) r2 ?_
  refine Executes.declare (restoreRest:=id) (offsetWords input 3) r3 ?_
  exact Executes.done _

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.payload_offset_read
#print axioms InitECandidate.Solver.Input.Payload.offset_declarations
