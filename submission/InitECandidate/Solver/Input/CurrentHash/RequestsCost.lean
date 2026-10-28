import InitECandidate.Solver.Input.CurrentHash.RequestsPipelineCost
import InitECandidate.Solver.Input.CurrentHash.RequestsAllocation
import InitECandidate.Solver.Input.CurrentHash.AllocationScopeCost
import InitECandidate.Solver.Input.WordPairEnvironment

namespace InitECandidate.Solver.Input.CurrentHash.RequestsHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def bodyPrice (size : Nat) := 13*(size-20)+19488

theorem after_mark_cost {input : Guest.InputBlob} (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (blob rq cursor chunk out zeros : BitVec 64) (start size : Nat) (counts : Nat→BitVec 64)
    (data : Before input source blob rq cursor chunk out zeros start size counts) (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source afterMark=(result,post)) (notTimeout : result≠some .timeOut) : source.clock-post.clock≤listPrices counts+3617 := by
  have total := AllocationScopeCost.cost source post cursor 160#64 data.context.installed data.context.heap data.context.heapBound "ch"
    [.panop .mul [.const 5#64,.const 32#64]] afterAllocation (listPrices counts+3615) rfl (by
      intro target room frame observed final evaluated notTimeout
      have ready := data.allocated room frame
      exact pipeline_cost RequestList.kinds (CallNormal.continuationEntry source target "ch" (.val (.word cursor))) final
        blob rq cursor (PersistentAlloc.rounded cursor 160#64) chunk out zeros start size counts ready observed evaluated notTimeout)
    result actual notTimeout
  omega

/-- Complete actual htr_requests body, including failed/partial allocations
and hash calls. Its decoded image is preserved only after each real normal
prefix; its five lists use one actual encoded request byte budget. -/
theorem body_cost {input : Guest.InputBlob} (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (blob rq cursor chunk out zeros : BitVec 64) (start size : Nat) (counts : Nat→BitVec 64)
    (data : Before input source blob rq cursor chunk out zeros start size counts) (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source body=(result,post)) (notTimeout : result≠some .timeOut) : source.clock-post.clock≤bodyPrice size := by
  rw [body_shape] at actual
  obtain ⟨funded,inner,remaining,endpoint⟩ := HeapScope.mark_call_trace source post cursor "mark" afterMark data.context.heap
    (HeapScope.mark_original_code source.code data.context.installed) result actual notTimeout
  let entry := bind {source with clock:=source.clock-1} "mark" cursor
  have kept (name : String) (different : ofString "mark"≠ofString name) := bind_lookup_other {source with clock:=source.clock-1} "mark" name cursor different
  have context : MerkleMemory.Context entry cursor zeros rq := data.context.of_frozen rfl
  have image : Requests.DecodedImage input entry blob rq start size counts := data.decoded.of_memory (by intro index inside; exact ⟨rfl,rfl⟩)
  have ready : Before input entry blob rq cursor chunk out zeros start size counts := ⟨context,image,(kept "rq" (by decide)).trans data.request,
    (kept "out" (by decide)).trans data.output,data.recordBefore,data.chunkCell,data.chunkArena,data.chunkAligned,data.chunkBefore⟩
  have priced := after_mark_cost entry inner blob rq cursor chunk out zeros start size counts ready result remaining notTimeout
  have budget := list_prices_budget data.decoded
  change source.clock-1-inner.clock≤listPrices counts+3617 at priced
  rw [endpoint]
  change source.clock-inner.clock≤bodyPrice size
  unfold bodyPrice
  omega

theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (Code.name .htr_requests)=some ([(ofString "rq",.one),(ofString "out",.one)],body,.one) := by
  simpa only [Code.formals,Code.body,Code.shape,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_htr_requests,body,paramToHOL,shapeToHOL,List.map_cons,List.map_nil]
    using Code.installed code installed .htr_requests

def values (rq out : BitVec 64) : List (ValueHOL 64) := [.val (.word rq),.val (.word out)]

/-- Actual two-word parent caller. All decoder, frontier and workspace facts
are current call-entry obligations, with no assumed future callee success. -/
theorem call_cost {input : Guest.InputBlob} (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (blob rq cursor chunk out zeros : BitVec 64) (start size : Nat) (counts : Nat→BitVec 64)
    (context : MerkleMemory.Context source cursor zeros rq) (decoded : Requests.DecodedImage input source blob rq start size counts)
    (recordBefore : rq.toNat+80≤cursor.toNat)
    (chunkCell : source.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk)))
    (chunkArena : AllocatedBytes.Arena chunk 32) (chunkAligned : chunk.toNat%8=0) (chunkBefore : chunk.toNat+32≤rq.toNat)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values rq out))
    (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (Code.name .htr_requests) arguments)=(result,post))
    (notTimeout : result≠some .timeOut) : source.clock-post.clock≤bodyPrice size+1 := by
  obtain ⟨callee,called,request,output⟩ := word_pair_environment source.code.lookup (Code.name .htr_requests) (ofString "rq") (ofString "out") body .one rq out
    (by decide) (original_code source.code context.installed)
  let entry := callEntryStateHOLFinite source callee
  have image : Requests.DecodedImage input entry blob rq start size counts := decoded.of_memory (by intro index inside; exact ⟨rfl,rfl⟩)
  have ready : Before input entry blob rq cursor chunk out zeros start size counts := ⟨context.at_callee callee,image,request,output,recordBefore,chunkCell,chunkArena,chunkAligned,chunkBefore⟩
  exact ClockCost.call_current_terminating source post destination (Code.name .htr_requests) arguments (values rq out) body callee .one (bodyPrice size) args called
    (fun observed target evaluated notTimeout=>body_cost entry target blob rq cursor chunk out zeros start size counts ready observed evaluated notTimeout) result actual notTimeout

end InitECandidate.Solver.Input.CurrentHash.RequestsHash

#print axioms InitECandidate.Solver.Input.CurrentHash.RequestsHash.after_mark_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestsHash.body_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestsHash.original_code
#print axioms InitECandidate.Solver.Input.CurrentHash.RequestsHash.call_cost
