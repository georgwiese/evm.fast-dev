import InitECandidate.Solver.Mpt.AccountNewCallNormal
import InitECandidate.Solver.Mpt.AccountNewCost
import InitECandidate.Solver.Input.ReturnNormal

namespace InitECandidate.Solver.Mpt.AccountEmpty
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open Input.RlpWrite

def zeroBalance : U256Value.Words := fun _=>0#64

/-- Original empty-account creation invokes the real constructor, derives
its allocation room and physical image, and retains the exact earlier frame. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap root hash : BitVec 64)
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word root)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word hash)))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapBound : heap.toNat≤33806089496) (heapAligned : heap.toNat%8=0)
    (domain : source.memaddrs=InitE.ordinaryDomain) (rootArena : AllocatedBytes.Arena root 32) (hashArena : AllocatedBytes.Arena hash 32)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    2≤source.clock ∧ heap.toNat+56≤33806089496 ∧ returned=.val (.word heap) ∧ post.clock=source.clock-2 ∧
      emptyLocalsHOLFinite post=emptyLocalsHOLFinite {source with
        globals:=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap 56#64)))
        memory:=AccountNew.finalMemory source.memory heap 0#64 zeroBalance root hash,clock:=source.clock-2} ∧
      (PersistentAlloc.rounded heap 56#64).toNat=heap.toNat+56 ∧ Nonempty (AccountDecode.Image post heap) ∧
      Rlp.Slices.Window source post heap.toNat (heap.toNat+56) ∧ HeapGlobals source post ∧
      post.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 56#64))) := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (AccountNew.values 0#64 zeroBalance hash) := by
    simp [arguments,AccountNew.values,zeroBalance,U256Value.tuple,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,hashGlobal]
  rw [body_shape] at normal
  obtain ⟨funded,room,ready,inner,cell,clock,frame,rounded,⟨image⟩,window,globals,heapAfter,tailRun,restored⟩ :=
    AccountNew.scoped_normal source post heap 0#64 zeroBalance root hash rootGlobal heapGlobal heapLower heapBound heapAligned domain rootArena hashArena installed
      "a" arguments (.return (localVar "a")) args returned normal
  have actual := Input.return_normal ready inner (localVar "a") returned tailRun
  have read : eval ready (localVar "a")=some (.val (.word heap)) := by simp [eval,localVar,evalHOLExact,toExact,cell]
  have returnedEq : returned=.val (.word heap) := Option.some.inj (actual.1.symm.trans read)
  have postEq : post=restore source "a" (emptyLocalsHOLFinite ready) := by rw [restored,actual.2]
  have postFrame : emptyLocalsHOLFinite post=emptyLocalsHOLFinite {source with
      globals:=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap 56#64)))
      memory:=AccountNew.finalMemory source.memory heap 0#64 zeroBalance root hash,clock:=source.clock-2} := by
    rw [postEq]
    change emptyLocalsHOLFinite ready=_
    exact frame
  refine ⟨funded,room,returnedEq,?_,postFrame,rounded,?_,?_,?_,?_⟩
  · rw [postEq]
    exact clock
  · exact ⟨AccountDecode.Image.of_agreement ready post heap image (by rw [postEq] <;> rfl) (by rw [postEq] <;> rfl) (by rw [postEq] <;> rfl)⟩
  · intro query outside
    rw [postEq]
    exact window query outside
  · rw [postEq]
    exact globals
  · rw [postEq]
    exact heapAfter

theorem body_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code body 3 := by
  rw [body_shape]
  exact Input.ClockCost.scoped_body code (ofString "a") .one (ofString "acct_new") arguments (.return (localVar "a"))
    AccountNew.formals AccountNew.body .one 2 0 (AccountNew.original_code code installed) (AccountNew.body_price code installed) (Input.ClockCost.returned code _)

end InitECandidate.Solver.Mpt.AccountEmpty

#print axioms InitECandidate.Solver.Mpt.AccountEmpty.body_normal
#print axioms InitECandidate.Solver.Mpt.AccountEmpty.body_price
