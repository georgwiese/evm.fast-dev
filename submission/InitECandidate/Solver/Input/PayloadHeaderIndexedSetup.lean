import InitECandidate.Solver.Input.PayloadHeaderIndexedEntry
import InitECandidate.Solver.Input.IgnoredCallTarget

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString Main

/-- The original guarded header's true transaction-trie call reaches the
real fresh empty-trie loop setup, with actual decoded ABI values and both
child/caller remainders retained. No constructor success is supplied. -/
theorem indexed_setup (input : Guest.InputBlob) (origin source current post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root header : BitVec 64) (counts : Nat→BitVec 64) (prepared : RequestRootHashData.Prepared input origin root counts)
    (physical : PhysicalHeader input origin source current root header)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState current afterSizeGuard=(some (.returned value),post)) :
    ∃ callee target returned loopInner after inner,
      callee.lookup (ofString "slice_arr")=some (.val (.word (PayloadHashData.description input).transactions)) ∧
      callee.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 (Payload.transactionCount input)))) ∧
      callee.lookup (ofString "out")=some (.val (.word (afterOmmerHeap header))) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite current callee) Mpt.Indexed.body=(some (.returned returned),target) ∧
      AllocatedBytes.Arena (headerFrontier header) 16 ∧ target.clock=loopInner.clock ∧
      evaluateHOLFiniteState (Mpt.Indexed.loopEntry (callEntryStateHOLFinite current callee) (headerFrontier header)) Mpt.Indexed.loopAndAfter=
        (some (.returned returned),loopInner) ∧
      after={target with locals:=current.locals} ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState after afterTransactionTrie=(some (.returned value),inner) := by
  rw [indexed_call_shape] at normal
  have never : NoReturn.Never (CallPrefix.program [.command indexedCall] .skip):=
    NoReturn.sequence _ _ (NoReturn.ignored_call _ _) NoReturn.skip
  obtain ⟨after,inner,execution,endpoint,remaining⟩:=CallPrefix.normal_trace current post [.command indexedCall] afterTransactionTrie value never normal
  obtain ⟨afterCall,callRun,next⟩:=execution.command_next indexedCall []
  have same : after=afterCall:=by cases next; rfl
  rw [same] at remaining
  have args:=indexed_arguments input origin source current root header counts prepared physical
  obtain ⟨callee,called,arrayLocal,countLocal,outLocal⟩:=Mpt.Indexed.environment current.code.lookup
    (PayloadHashData.description input).transactions (BitVec.ofNat 64 (Payload.transactionCount input)) (afterOmmerHeap header)
    (Mpt.Indexed.original_code current.code physical.installed)
  obtain ⟨funded,target,returned,childRun⟩:=CallNormal.ignored_callee_return current afterCall (ofString "build_mpt_indexed") indexedArguments
    (Mpt.Indexed.values (PayloadHashData.description input).transactions (BitVec.ofNat 64 (Payload.transactionCount input)) (afterOmmerHeap header))
    Mpt.Indexed.body callee .one args called callRun
  obtain ⟨arena,loopInner,childEndpoint,loopRun⟩:=Mpt.Indexed.normal_setup (callEntryStateHOLFinite current callee) target (headerFrontier header)
    physical.installed physical.frontier.cell physical.domain physical.frontier.arena physical.frontier.aligned returned childRun
  have callerPost:=CallNormal.ignored_target current afterCall (ofString "build_mpt_indexed") indexedArguments
    (Mpt.Indexed.values (PayloadHashData.description input).transactions (BitVec.ofNat 64 (Payload.transactionCount input)) (afterOmmerHeap header))
    Mpt.Indexed.body callee .one args called returned target childRun callRun
  exact ⟨callee,target,returned,loopInner,afterCall,inner,arrayLocal,countLocal,outLocal,childRun,arena,childEndpoint,loopRun,callerPost,endpoint,remaining⟩

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.indexed_setup
