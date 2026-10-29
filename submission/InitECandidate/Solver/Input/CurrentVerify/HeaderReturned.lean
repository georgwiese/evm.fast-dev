import InitECandidate.Solver.Input.CurrentVerify.HeaderContext
import InitECandidate.Solver.Input.CallResumeLookup

namespace InitECandidate.Solver.Input.CurrentVerify.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- A genuine validator return preserves main's physical SI/payload/gas and
all witness images, and supplies its actual advanced heap/hash environment
before the original after-header continuation starts. -/
theorem after_headers_data {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord array heap count nextHeap : BitVec 64} {pointers lengths : Nat→BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (sourceHeap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (returned : Headers.CurrentValidate.Returned source target array heap count 2701132160#64 2701132360#64 nextHeap pointers lengths 2701134824 boundary) :
    Data input (CallNormal.continuationEntry source target "vh" (Headers.CurrentValidate.result heap (Headers.CurrentValidate.hashesPointer heap count)))
      pointer si record gasWord boundary := by
  let ready:=CallNormal.continuationEntry source target "vh" (Headers.CurrentValidate.result heap (Headers.CurrentValidate.hashesPointer heap count))
  have arena : CurrentStartup.ArenaState ready := returned.context.arena.of_frame rfl
  have environment : CurrentKeccak.Hash.Environment ready 2701132160#64 2701132360#64 := returned.context.environment.of_frame rfl
  have little : ready.be=false := returned.metadata.2.1.trans data.little
  obtain ⟨cursor,cell,lower,upper,aligned⟩:=data.heap
  have cursorEq : cursor=heap := by
    have equal:=Option.some.inj (cell.symm.trans sourceHeap)
    cases equal
    rfl
  subst cursor
  have nextHeapData : NormalHeapEffects.AtLeast (boundary+32) ready :=
    ⟨nextHeap,returned.context.heapCell,by have h:=returned.heapAfter; omega,returned.context.heapBound,returned.context.heapAligned⟩
  have siLocal : ready.locals.lookup (ofString "si")=some (.val (.word si)) :=
    (CallNormal.continuation_lookup_other source target "vh" "si" _ (by decide)).trans data.siLocal
  exact data.of_interval arena little environment
    ((returned.globals (ofString "mpt_hash_scratch") (by decide)).trans data.mptHash) ((returned.globals (ofString "mpt_key_scratch") (by decide)).trans data.mptKey) ((returned.globals (ofString "empty_trie_root") (by decide)).trans data.mptEmpty)
    ((returned.globals _ (by decide)).trans data.shaState) ((returned.globals _ (by decide)).trans data.shaPad) nextHeapData siLocal
    (fun query low high=>returned.input.words query low high)

/-- The actual reached after-header continuation has main's full physical
inputs. Both the validator's paid clock and the final original lexical
restoration are retained on every enclosing outcome. -/
theorem header_data_trace {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤51528323 ∨ ∃ current inner,
      Data input current pointer si record gasWord boundary ∧ current.locals.lookup (ofString "pl")=some (.val (.word record)) ∧ current.clock≤source.clock ∧
      source.clock-current.clock≤51528323 ∧
      evaluateHOLFiniteState current afterHeaders=(outcome,inner) ∧ post.clock=inner.clock ∧
      LocalEffects.erase post=LocalEffects.erase inner := by
  rcases header_trace data outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨array,start,length,heap,target,nextHeap,inner,returned,heapCell,continued,endpoint⟩:=reached
    have nextSi := (bind_lookup_other source "pl" "si" record (by decide)).trans data.siLocal
    have entryData := data.of_frame (post:=bind source "pl" record) rfl nextSi
    have nextData := after_headers_data entryData heapCell returned
    let current := CallNormal.continuationEntry (bind source "pl" record) target "vh"
      (Headers.CurrentValidate.result heap (Headers.CurrentValidate.hashesPointer heap (BitVec.ofNat 64 (VarList.decodedCount input start length))))
    have payloadLocal : current.locals.lookup (ofString "pl")=some (.val (.word record)):=
      (CallNormal.continuation_lookup_other (bind source "pl" record) target "vh" "pl"
        (Headers.CurrentValidate.result heap (Headers.CurrentValidate.hashesPointer heap (BitVec.ofNat 64 (VarList.decodedCount input start length)))) (by decide)).trans (bind_lookup_same _ _ _)
    exact Or.inr ⟨current,inner,nextData,payloadLocal,returned.forward,returned.cost,continued,by rw [endpoint]; rfl,by rw [endpoint]; rfl⟩

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.after_headers_data

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.header_data_trace
