import InitECandidate.Solver.Mpt.NodeRlpBeginAllocation

namespace InitECandidate.Solver.Mpt.NodeRlpBegin
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open KeyToNibbles (SpanFrame)

theorem after_allocation_safe (key : MlS) (notFlag : key≠ofString "isl") (notLength : key≠ofString "clen")
    (notPayload : key≠ofString "payload") (notEncoded : key≠ofString "el") (notValue : key≠ofString "vl") :
    Input.LocalPrefix key afterAllocation := by
  rw [path_shapes.2.2.1,path_shapes.2.2.2.1]
  exact .dec _ _ _ notFlag (.seq (.ite _ (.assign _ _ notFlag) .skip) (compact_phase_safe key notLength notPayload notEncoded notValue))

/-- Entire actual allocation/flag/compact/size path. Failed allocation
and byte operations retain their own bounds; continuation facts are derived
only from real successful prefixes. -/
theorem after_path_length_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node tag pathLength : BitVec 64)
    (limit : Nat) (property : BitVec 64→BitVec 64→Prop) (data : PathInput source node tag pathLength limit property)
    (fits : pathLength.toNat/2+limit+19<2^64) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterPathLength).2.clock≤pathLength.toNat/2+26 := by
  rw [path_shapes.2.1]
  have price:=Input.ClockCost.sequence_reached_current source allocationCall afterAllocation 2 (pathLength.toNat/2+24)
    (Input.ClockCost.call_body source.code (some (some (ofString "cbuf"))) (ofString "alloc") allocationArguments PersistentAlloc.formals PersistentAlloc.body .one 1
      (PersistentAlloc.original_code source.code installed) (PersistentAlloc.body_price source.code installed) source rfl) (by
        intro current run
        obtain ⟨_room,endpoint,⟨next⟩⟩:=after_real_allocation source current node tag pathLength limit property data installed run
        exact after_allocation_cost current node tag data.heap pathLength limit property next fits (by rw [endpoint]; exact installed))
  change source.clock-(evaluateHOLFiniteState source (.seq allocationCall afterAllocation)).2.clock≤_
  omega

/-- A genuine normal complete path phase derives its allocated arena,
actual lengths and payload and preserves every older persistent word. The
frame retains the real updated heap global and every other nonlocal field. -/
theorem after_path_length_normal_exact (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (node tag pathLength : BitVec 64)
    (limit : Nat) (property : BitVec 64→BitVec 64→Prop) (data : PathInput source node tag pathLength limit property)
    (fits : pathLength.toNat/2+limit+19<2^64) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source afterPathLength=(none,target)) :
    (∃ length payload : BitVec 64,target.locals.lookup (ofString "clen")=some (.val (.word length)) ∧ length.toNat=pathLength.toNat/2+1 ∧
      target.locals.lookup (ofString "payload")=some (.val (.word payload)) ∧ pathLength.toNat/2+1≤payload.toNat ∧ payload.toNat≤pathLength.toNat/2+limit+19 ∧ PathPayload target node tag data.heap length payload) ∧
      target.locals.lookup (ofString "cbuf")=some (.val (.word data.heap)) ∧
      data.heap.toNat+pathLength.toNat/2+2≤2952790016 ∧
      SpanFrame (PersistentAlloc.post source data.heap (allocationAmount pathLength)) target data.heap (pathLength.toNat/2+1) ∧
      (∀ query : BitVec 64,query.toNat<data.heap.toNat→target.memory query=source.memory query) := by
  rw [path_shapes.2.1] at normal
  obtain ⟨current,allocationRun,continued⟩:=Input.sequence_none source target allocationCall afterAllocation normal
  obtain ⟨room,endpoint,⟨next⟩⟩:=after_real_allocation source current node tag pathLength limit property data installed allocationRun
  obtain ⟨result,frame⟩:=after_allocation_normal_exact current target node tag data.heap pathLength limit property next fits (by rw [endpoint]; exact installed) continued
  have saved:=(after_allocation_safe (ofString "cbuf") (by decide) (by decide) (by decide) (by decide) (by decide)).summary_full current
  unfold Input.LocalSummary at saved
  rw [continued] at saved
  have currentBuffer : current.locals.lookup (ofString "cbuf")=some (.val (.word data.heap)):=by
    rw [endpoint]
    exact bind_lookup_same _ _ _
  have resultFrame : SpanFrame (PersistentAlloc.post source data.heap (allocationAmount pathLength)) target data.heap (pathLength.toNat/2+1):=by
    rw [endpoint] at frame
    exact ⟨frame.fields,frame.memory⟩
  refine ⟨result,(saved.1 rfl).trans currentBuffer,room,resultFrame,?_⟩
  intro query older
  exact resultFrame.memory query (fun offset inside=>fresh_output_away data.heap query (pathLength.toNat/2+2) offset data.heapAligned older (by omega) (by omega))

theorem after_path_length_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (node tag pathLength : BitVec 64)
    (limit : Nat) (property : BitVec 64→BitVec 64→Prop) (data : PathInput source node tag pathLength limit property)
    (fits : pathLength.toNat/2+limit+19<2^64) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source afterPathLength=(none,target)) :
    (∃ length payload : BitVec 64,target.locals.lookup (ofString "clen")=some (.val (.word length)) ∧ length.toNat=pathLength.toNat/2+1 ∧
      target.locals.lookup (ofString "payload")=some (.val (.word payload)) ∧ pathLength.toNat/2+1≤payload.toNat ∧ payload.toNat≤pathLength.toNat/2+limit+19) ∧
      target.locals.lookup (ofString "cbuf")=some (.val (.word data.heap)) ∧
      data.heap.toNat+pathLength.toNat/2+2≤2952790016 ∧
      SpanFrame (PersistentAlloc.post source data.heap (allocationAmount pathLength)) target data.heap (pathLength.toNat/2+1) ∧
      (∀ query : BitVec 64,query.toNat<data.heap.toNat→target.memory query=source.memory query) := by
  obtain ⟨⟨length,payload,cell,size,pay,lower,upper,_sized⟩,buffer,room,frame,older⟩:=after_path_length_normal_exact source target node tag pathLength limit property data fits installed normal
  exact ⟨⟨length,payload,cell,size,pay,lower,upper⟩,buffer,room,frame,older⟩

end InitECandidate.Solver.Mpt.NodeRlpBegin

#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.after_allocation_safe
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.after_path_length_cost
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.after_path_length_normal

#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.after_path_length_normal_exact
