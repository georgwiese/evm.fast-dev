import InitECandidate.Solver.Input.CurrentHash.RootPipelineCost
import InitECandidate.Solver.Input.CurrentHash.RootAllocation
import InitECandidate.Solver.Input.CurrentHash.AllocationScopeCost

set_option maxRecDepth 20000
set_option maxHeartbeats 200000

namespace InitECandidate.Solver.Input.CurrentHash.RootHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

variable {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {blob si record rq root array : BitVec 64} {length start size : Nat}

def bodyPrice (input : Guest.InputBlob) (length start size : Nat) := pipelinePrice steps input length start size+413

theorem after_mark_cost (data : Invocation.Data input source blob si record rq root array length start size) (cursor : BitVec 64)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor))) (rootBefore : root.toNat+32≤cursor.toNat)
    (bounded : cursor.toNat≤2952790016) (aligned : cursor.toNat%8=0)
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source afterMark=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤pipelinePrice steps input length start size+412 := by
  rw [source_shape.2.1] at actual
  have paid := AllocationScopeCost.cost source post cursor 128#64 data.workspace.code heap bounded "ch" [.panop .mul [.const 4#64,.const 32#64]] afterAllocation
    (pipelinePrice steps input length start size+410) rfl
    (by intro target room same observed final evaluated noTimeout
        have next := allocated data rootBefore bounded aligned room same
        rw [source_shape.2.2] at evaluated
        have paid := pipeline_cost (post:=final) steps next observed evaluated noTimeout
        exact paid) result actual notTimeout
  have arithmetic : ∀ k : Nat,(k+410)+2≤k+412 := by intro k; omega
  exact Nat.le_trans paid (arithmetic _)

/-- Complete unchanged current htr_new_payload_request body, including the
actual saved mark/chunk allocation, all four child calls, Merkle and release.
Every continuing call supplies the next decoded image; all observed non-timeout
allocation failures and other stopped prefixes are included. -/
theorem body_cost (data : Invocation.Data input source blob si record rq root array length start size)
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source body=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤bodyPrice input length start size := by
  obtain ⟨cursor,heap,rootBefore,bounded,aligned⟩ := data.heap
  rw [source_shape.1] at actual
  obtain ⟨funded,inner,remaining,endpoint⟩ := HeapScope.mark_call_trace source post cursor "mark" afterMark heap
    (HeapScope.mark_original_code source.code data.workspace.code) result actual notTimeout
  let entry := bind {source with clock:=source.clock-1} "mark" cursor
  have next : Invocation.Data input entry blob si record rq root array length start size := (data.at_clock (source.clock-1)).bound "mark" cursor (by decide)
  have paid := after_mark_cost (post:=inner) next cursor heap rootBefore bounded aligned result remaining notTimeout
  change source.clock-1-inner.clock≤pipelinePrice steps input length start size+412 at paid
  rw [endpoint]
  change source.clock-inner.clock≤bodyPrice input length start size
  unfold bodyPrice
  omega


end InitECandidate.Solver.Input.CurrentHash.RootHash

#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.after_mark_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.body_cost
