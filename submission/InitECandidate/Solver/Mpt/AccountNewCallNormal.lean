import InitECandidate.Solver.Mpt.AccountNewNormal
import InitECandidate.Solver.Mpt.AccountNewEnvironment
import InitECandidate.Solver.Input.NormalCallEntry

namespace InitECandidate.Solver.Mpt.AccountNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open Input.RlpWrite

/-- The real original account-constructor caller delivers the fresh image
and exact allocation/store frame at its actual continuation. -/
theorem scoped_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap nonce : BitVec 64) (balance : U256Value.Words) (root hash : BitVec 64)
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word root)))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapBound : heap.toNat≤33806089496) (heapAligned : heap.toNat%8=0)
    (domain : source.memaddrs=InitE.ordinaryDomain) (rootArena : AllocatedBytes.Arena root 32) (hashArena : AllocatedBytes.Arena hash 32)
    (installed : Input.OriginalCode.Installed source.code)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values nonce balance hash))
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "acct_new") arguments continuation)=(some (.returned returned),post)) :
    2≤source.clock ∧ heap.toNat+56≤33806089496 ∧ ∃ ready inner,
      ready.locals.lookup (ofString name)=some (.val (.word heap)) ∧ ready.clock=source.clock-2 ∧
      emptyLocalsHOLFinite ready=emptyLocalsHOLFinite {source with
        globals:=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap 56#64)))
        memory:=finalMemory source.memory heap nonce balance root hash,clock:=source.clock-2} ∧
      (PersistentAlloc.rounded heap 56#64).toNat=heap.toNat+56 ∧ Nonempty (AccountDecode.Image ready heap) ∧
      Rlp.Slices.Window source ready heap.toNat (heap.toNat+56) ∧ HeapGlobals source ready ∧
      ready.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 56#64))) ∧
      evaluateHOLFiniteState ready continuation=(some (.returned returned),inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called,nonceCell,balanceCell,hashCell⟩ := environment source.code.lookup nonce balance hash (original_code source.code installed)
  obtain ⟨positive,target,answer,inner,bodyRun,checked,tailRun,restored⟩ := Input.CallNormal.scoped_normal source post name .one (ofString "acct_new")
    arguments _ body continuation callee .one args called returned normal
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨funded,room,answerEq,clock,frame,rounded,image,window,globals,heapAfter⟩ := body_normal entry target heap nonce balance root hash
    nonceCell balanceCell hashCell rootGlobal heapGlobal heapLower heapBound heapAligned domain rootArena hashArena installed answer bodyRun
  rw [answerEq] at tailRun
  let ready := Input.CallNormal.continuationEntry source target name (.val (.word heap))
  change 1≤source.clock-1 at funded
  change target.clock=source.clock-1-1 at clock
  have readyClock : ready.clock=source.clock-2 := by change target.clock=source.clock-2; omega
  have readyFrame : emptyLocalsHOLFinite ready=emptyLocalsHOLFinite {source with
      globals:=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap 56#64)))
      memory:=finalMemory source.memory heap nonce balance root hash,clock:=source.clock-2} := by
    change emptyLocalsHOLFinite target=_
    rw [frame]
    change emptyLocalsHOLFinite {source with globals:=_,memory:=_,clock:=source.clock-1-1}=_
    have subtract : source.clock-1-1=source.clock-2 := by omega
    rw [subtract]
    rfl
  have readyImage : Nonempty (AccountDecode.Image ready heap) := by
    obtain ⟨current⟩ := image
    exact ⟨AccountDecode.Image.of_agreement target ready heap current rfl rfl rfl⟩
  exact ⟨by omega,room,ready,inner,Input.CallNormal.continuation_lookup_same source target name (.val (.word heap)),readyClock,readyFrame,rounded,
    readyImage,window,globals,heapAfter,tailRun,restored⟩

end InitECandidate.Solver.Mpt.AccountNew

#print axioms InitECandidate.Solver.Mpt.AccountNew.scoped_normal
