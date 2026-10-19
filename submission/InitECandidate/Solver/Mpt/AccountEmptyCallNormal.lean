import InitECandidate.Solver.Mpt.AccountEmptyNormal
import InitECandidate.Solver.Input.ScopedCallNormal

namespace InitECandidate.Solver.Mpt.AccountEmpty
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem environment (codeFn : MlS → Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL))
    (lookup : codeFn (ofString "acct_empty")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "acct_empty") []=some (body,callee,.one) := by
  have raw : lookupCodeHOLExact codeFn (ofString "acct_empty") []=some (body,(fun _=>none),.one) := by
    simp [lookupCodeHOLExact,lookup,formals]
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  exact ⟨callee,called⟩

/-- Original nullary empty-account caller, with its actual fresh image,
exact three source ticks and real continuation state. -/
theorem scoped_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap root hash : BitVec 64)
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word root)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word hash)))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapBound : heap.toNat≤33806089496) (heapAligned : heap.toNat%8=0)
    (domain : source.memaddrs=InitE.ordinaryDomain) (rootArena : AllocatedBytes.Arena root 32) (hashArena : AllocatedBytes.Arena hash 32)
    (installed : Input.OriginalCode.Installed source.code)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [])
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "acct_empty") expressions continuation)=(some (.returned returned),post)) :
    3≤source.clock ∧ heap.toNat+56≤33806089496 ∧ ∃ ready inner,
      ready.locals.lookup (ofString name)=some (.val (.word heap)) ∧ ready.clock=source.clock-3 ∧
      emptyLocalsHOLFinite ready=emptyLocalsHOLFinite {source with
        globals:=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap 56#64)))
        memory:=AccountNew.finalMemory source.memory heap 0#64 zeroBalance root hash,clock:=source.clock-3} ∧
      (PersistentAlloc.rounded heap 56#64).toNat=heap.toNat+56 ∧ Nonempty (AccountDecode.Image ready heap) ∧
      Rlp.Slices.Window source ready heap.toNat (heap.toNat+56) ∧ HeapGlobals source ready ∧
      ready.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 56#64))) ∧
      evaluateHOLFiniteState ready continuation=(some (.returned returned),inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called⟩ := environment source.code.lookup (original_code source.code installed)
  obtain ⟨positive,target,answer,inner,bodyRun,checked,tailRun,restored⟩ := Input.CallNormal.scoped_normal source post name .one (ofString "acct_empty")
    expressions [] body continuation callee .one args called returned normal
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨funded,room,answerEq,clock,frame,rounded,image,window,globals,heapAfter⟩ := body_normal entry target heap root hash rootGlobal hashGlobal heapGlobal
    heapLower heapBound heapAligned domain rootArena hashArena installed answer bodyRun
  rw [answerEq] at tailRun
  let ready := Input.CallNormal.continuationEntry source target name (.val (.word heap))
  change 2≤source.clock-1 at funded
  change target.clock=source.clock-1-2 at clock
  have readyClock : ready.clock=source.clock-3 := by change target.clock=source.clock-3; omega
  have readyFrame : emptyLocalsHOLFinite ready=emptyLocalsHOLFinite {source with
      globals:=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap 56#64)))
      memory:=AccountNew.finalMemory source.memory heap 0#64 zeroBalance root hash,clock:=source.clock-3} := by
    change emptyLocalsHOLFinite target=_
    rw [frame]
    change emptyLocalsHOLFinite {source with globals:=_,memory:=_,clock:=source.clock-1-2}=_
    have subtract : source.clock-1-2=source.clock-3 := by omega
    rw [subtract] <;> rfl
  have readyImage : Nonempty (AccountDecode.Image ready heap) := by
    obtain ⟨current⟩ := image
    exact ⟨AccountDecode.Image.of_agreement target ready heap current rfl rfl rfl⟩
  exact ⟨by omega,room,ready,inner,Input.CallNormal.continuation_lookup_same source target name (.val (.word heap)),readyClock,readyFrame,rounded,
    readyImage,window,globals,heapAfter,tailRun,restored⟩

end InitECandidate.Solver.Mpt.AccountEmpty

#print axioms InitECandidate.Solver.Mpt.AccountEmpty.environment
#print axioms InitECandidate.Solver.Mpt.AccountEmpty.scoped_normal
