import InitECandidate.Solver.Headers.CurrentValidate.AfterHeader
import InitECandidate.Solver.Headers.CurrentDecode.ScopedNone
import InitECandidate.Solver.Headers.CurrentValidate.HeaderReturned

namespace InitECandidate.Solver.Headers.CurrentValidate
open Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def decodePrice (bytes : Nat) := 195*bytes+474+(44*(bytes/136)+690)

theorem RoundState.header_context (data : Data) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : RoundState data origin source index) (layout : RoundLayout data) (inside : index<data.count) :
    ∃ heap,source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧ heap.toNat≤2952790016 ∧ heap.toNat%8=0 ∧
      (data.pointers index).toNat+(data.lengths index).toNat≤heap.toNat ∧ 2701131776≤heap.toNat := by
  obtain ⟨heap,cell,bound,aligned,hashesBefore⟩ := state.heap
  have inputBefore:=state.rows.inputBefore index inside
  have inputAfter:=state.rows.inputAfter index inside
  have a:=layout.inputBefore
  have b:=layout.hsBeforeHashes
  have lower:=layout.lower
  exact ⟨heap,cell,bound,aligned,by omega,by omega⟩

/-- Complete original per-header iteration: actual decode_header, pointer
publication, raw-byte Keccak and counter update, on every outcome. -/
theorem decode_step_cost (data : Data) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : RoundState data origin source index) (layout : RoundLayout data) (inside : index<data.count) :
    source.clock-(evaluateHOLFiniteState source decodeStep).2.clock≤decodePrice (data.lengths index).toNat := by
  obtain ⟨heap,heapCell,heapBound,heapAligned,before,lower⟩ := state.header_context data origin source index layout inside
  have args:=state.rows.read source data.array data.pointers data.lengths data.count data.lower data.upper index inside state.arena.domain state.arrayCell state.indexCell
  obtain ⟨_,_,_,_,_,_,_,decodeShape,_,_,_⟩ := shapes
  let post:=(evaluateHOLFiniteState source decodeStep).2
  let result:=(evaluateHOLFiniteState source decodeStep).1
  have run : evaluateHOLFiniteState source decodeStep=(result,post) := rfl
  change source.clock-post.clock≤_
  rw [decodeShape] at run
  rcases CurrentDecode.scoped_trace source post (data.pointers index) (data.lengths index) heap state.arena heapCell heapBound lower heapAligned before
    "h" decodeArguments afterHeader args result run with stopped|reached
  · exact Nat.le_trans stopped (Nat.le_add_right _ _)
  · obtain ⟨target,header,inner,returned,continued,endpoint⟩ := reached
    let ready:=Input.CallNormal.continuationEntry source target "h" (.val (.word header))
    have next:=state.after_header data origin source target index layout heap header heapCell returned
    have headerCell : ready.locals.lookup (ofString "h")=some (.val (.word header)) := by
      simp [ready,Input.CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
    have tailCost:=after_header_cost data origin ready index next layout inside header headerCell
    rw [continued] at tailCost
    have tailClock:=evaluateHOLFiniteState_clock_le ready afterHeader
    rw [continued] at tailClock
    have finalClock : post.clock=inner.clock := by rw [endpoint]; rfl
    change target.clock-inner.clock≤_ at tailCost
    change inner.clock≤target.clock at tailClock
    have cost:=returned.cost
    have forward:=returned.forward
    rw [finalClock]
    unfold decodePrice
    omega

theorem decode_step_normal (data : Data) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : RoundState data origin source index) (layout : RoundLayout data) (inside : index<data.count)
    (normal : evaluateHOLFiniteState source decodeStep=(none,post)) : RoundState data origin post (index+1) := by
  obtain ⟨heap,heapCell,heapBound,heapAligned,before,lower⟩ := state.header_context data origin source index layout inside
  have args:=state.rows.read source data.array data.pointers data.lengths data.count data.lower data.upper index inside state.arena.domain state.arrayCell state.indexCell
  obtain ⟨_,_,_,_,_,_,_,decodeShape,_,_,_⟩ := shapes
  rw [decodeShape] at normal
  obtain ⟨target,header,inner,returned,continued,endpoint⟩ := CurrentDecode.scoped_none source post (data.pointers index) (data.lengths index) heap
    state.arena heapCell heapBound lower heapAligned before "h" decodeArguments afterHeader args normal
  let ready:=Input.CallNormal.continuationEntry source target "h" (.val (.word header))
  have next:=state.after_header data origin source target index layout heap header heapCell returned
  have headerCell : ready.locals.lookup (ofString "h")=some (.val (.word header)) := by
    simp [ready,Input.CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have finalState:=after_header_normal data origin ready inner index next layout inside header headerCell continued
  rw [endpoint]
  exact finalState.restore_temporary data origin source inner (index+1) "h" (Or.inl rfl)

end InitECandidate.Solver.Headers.CurrentValidate

#print axioms InitECandidate.Solver.Headers.CurrentValidate.RoundState.header_context
#print axioms InitECandidate.Solver.Headers.CurrentValidate.decode_step_cost
#print axioms InitECandidate.Solver.Headers.CurrentValidate.decode_step_normal

namespace InitECandidate.Solver.Headers.CurrentValidate

theorem decode_price_limit (data : Data) (layout : RoundLayout data) (index : Nat) (inside : index<data.count) :
    decodePrice (data.lengths index).toNat≤201152 := by
  have h:=layout.lengths index inside
  unfold decodePrice
  omega

end InitECandidate.Solver.Headers.CurrentValidate

#print axioms InitECandidate.Solver.Headers.CurrentValidate.decode_price_limit
