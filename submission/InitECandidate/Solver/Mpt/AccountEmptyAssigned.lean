import InitECandidate.Solver.Mpt.AccountEmptyCallNormal
import InitECandidate.Solver.Mpt.AccountRegistryFresh
import InitECandidate.Solver.Input.AssignedCallData

namespace InitECandidate.Solver.Mpt.AccountEmpty
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def assignedTarget (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap root hash : BitVec 64) (name : MlS) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  setVarHOLFinite name (.val (.word heap)) {source with
    globals:=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap 56#64)))
    memory:=AccountNew.finalMemory source.memory heap 0#64 zeroBalance root hash,clock:=source.clock-3}

/-- Actual assigned empty-account call used by the original getter fallback.
The return value, assignment and complete nonlocal effect are derived from
the real callee; no prospective assignment result or funding is supplied. -/
theorem assigned_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap root hash : BitVec 64)
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word root)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word hash)))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapBound : heap.toNat≤33806089496) (heapAligned : heap.toNat%8=0)
    (domain : source.memaddrs=InitE.ordinaryDomain) (rootArena : AllocatedBytes.Arena root 32) (hashArena : AllocatedBytes.Arena hash 32)
    (installed : Input.OriginalCode.Installed source.code) (name : MlS) (expressions : List (ExpHOL 64))
    (expectedArgs : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [])
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,name),none)) (ofString "acct_empty") expressions)=(none,post)) :
    3≤source.clock ∧ heap.toNat+56≤33806089496 ∧ post=assignedTarget source heap root hash name ∧
      post.locals.lookup name=some (.val (.word heap)) ∧ post.clock=source.clock-3 ∧
      (PersistentAlloc.rounded heap 56#64).toNat=heap.toNat+56 ∧ Nonempty (AccountDecode.Image post heap) ∧
      Rlp.Slices.Window source post heap.toNat (heap.toNat+56) ∧ HeapGlobals source post ∧
      post.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 56#64))) := by
  obtain ⟨positive,values,actual,callee,returnShape,target,returned,args,called,bodyRun,checked,postEq⟩ :=
    Input.CallNormal.local_data source post name (ofString "acct_empty") expressions normal
  have valuesEq := Option.some.inj (args.symm.trans expectedArgs)
  rw [valuesEq] at called
  obtain ⟨expected,known⟩ := environment source.code.lookup (original_code source.code installed)
  have bodyEq := congrArg Prod.fst (Option.some.inj (called.symm.trans known))
  change actual=body at bodyEq
  rw [bodyEq] at bodyRun
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨funded,room,returnedEq,clock,frame,rounded,image,window,globals,heapAfter⟩ := body_normal entry target heap root hash rootGlobal hashGlobal heapGlobal
    heapLower heapBound heapAligned domain rootArena hashArena installed returned bodyRun
  rw [returnedEq] at postEq
  change 2≤source.clock-1 at funded
  have subtract : source.clock-1-2=source.clock-3 := by omega
  have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) frame
  change {target with locals:=source.locals}={source with
    globals:=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap 56#64)))
    memory:=AccountNew.finalMemory source.memory heap 0#64 zeroBalance root hash,clock:=source.clock-1-2} at callerFrame
  have canonical : post=assignedTarget source heap root hash name := by
    rw [postEq,callerFrame,subtract]
    rfl
  refine ⟨by omega,room,canonical,?_,?_,rounded,?_,?_,?_,?_⟩
  · rw [canonical]
    simp [assignedTarget,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  · rw [canonical]
    rfl
  · obtain ⟨current⟩ := image
    exact ⟨AccountDecode.Image.of_agreement target post heap current (by rw [postEq] <;> rfl) (by rw [postEq] <;> rfl) (by rw [postEq] <;> rfl)⟩
  · intro query outside
    rw [postEq]
    exact window query outside
  · rw [postEq]
    exact globals
  · rw [postEq]
    exact heapAfter

end InitECandidate.Solver.Mpt.AccountEmpty

#print axioms InitECandidate.Solver.Mpt.AccountEmpty.assigned_normal
