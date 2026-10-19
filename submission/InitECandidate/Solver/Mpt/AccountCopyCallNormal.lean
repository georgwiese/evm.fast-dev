import InitECandidate.Solver.Mpt.AccountCopyNormal
import InitECandidate.Solver.Input.UnaryCallData
import InitECandidate.Solver.Input.ScopedCallNormal

namespace InitECandidate.Solver.Mpt.AccountCopy
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The actual original copying caller derives the exact copied account,
seven source ticks and a complete fresh-allocation frame at its continuation. -/
theorem scoped_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (account heap : BitVec 64)
    (image : AccountDecode.Image source account) (earlier : account.toNat+56≤heap.toNat)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (heapAligned : heap.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word account)])
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "acct_copy") expressions continuation)=(some (.returned returned),post)) :
    7≤source.clock ∧ heap.toNat+56≤33806089496 ∧ ∃ ready inner,
      ready.locals.lookup (ofString name)=some (.val (.word heap)) ∧ ready.clock=source.clock-7 ∧
      emptyLocalsHOLFinite ready=emptyLocalsHOLFinite {source with
        globals:=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap 56#64)))
        memory:=CopyGeneral.resultMemory source.memory source.be account heap 56,clock:=source.clock-7} ∧
      (PersistentAlloc.rounded heap 56#64).toNat=heap.toNat+56 ∧ Nonempty (AccountDecode.Image ready heap) ∧
      Rlp.Slices.Window source ready heap.toNat (heap.toNat+56) ∧ HeapGlobals source ready ∧
      ready.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 56#64))) ∧
      evaluateHOLFiniteState ready continuation=(some (.returned returned),inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called,accountCell⟩ := Input.CallNormal.unary_environment source.code.lookup (ofString "acct_copy") "a" body account (original_code source.code installed)
  obtain ⟨positive,target,answer,inner,bodyRun,checked,tailRun,restored⟩ := Input.CallNormal.scoped_normal source post name .one (ofString "acct_copy")
    expressions _ body continuation callee .one args called returned normal
  let entry := callEntryStateHOLFinite source callee
  let entryImage := AccountDecode.Image.of_agreement source entry account image rfl rfl rfl
  obtain ⟨funded,room,answerEq,clock,frame,rounded,nextImage,window,globals,heapAfter⟩ := body_normal entry target account heap accountCell entryImage earlier heapGlobal
    heapBound heapAligned installed answer bodyRun
  rw [answerEq] at tailRun
  let ready := Input.CallNormal.continuationEntry source target name (.val (.word heap))
  change 6≤source.clock-1 at funded
  change target.clock=source.clock-1-6 at clock
  have readyClock : ready.clock=source.clock-7 := by change target.clock=source.clock-7; omega
  have readyFrame : emptyLocalsHOLFinite ready=emptyLocalsHOLFinite {source with
      globals:=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap 56#64)))
      memory:=CopyGeneral.resultMemory source.memory source.be account heap 56,clock:=source.clock-7} := by
    change emptyLocalsHOLFinite target=_
    rw [frame]
    change emptyLocalsHOLFinite {source with globals:=_,memory:=_,clock:=source.clock-1-6}=_
    have subtract : source.clock-1-6=source.clock-7 := by omega
    rw [subtract] <;> rfl
  have readyImage : Nonempty (AccountDecode.Image ready heap) := by
    obtain ⟨current⟩ := nextImage
    exact ⟨AccountDecode.Image.of_agreement target ready heap current rfl rfl rfl⟩
  exact ⟨by omega,room,ready,inner,Input.CallNormal.continuation_lookup_same source target name (.val (.word heap)),readyClock,readyFrame,rounded,
    readyImage,window,globals,heapAfter,tailRun,restored⟩

end InitECandidate.Solver.Mpt.AccountCopy

#print axioms InitECandidate.Solver.Mpt.AccountCopy.scoped_normal
