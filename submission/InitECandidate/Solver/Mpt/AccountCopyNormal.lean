import InitECandidate.Solver.Mpt.AccountNewProgram
import InitECandidate.Solver.Mpt.AccountCopyImage
import InitECandidate.Solver.WitnessRadix.AllocationCallNormal
import InitECandidate.Solver.WitnessRadix.AllocationCost
import InitECandidate.Solver.WitnessRadix.CopyNormalCall
import InitECandidate.Solver.WitnessRadix.CopyGeneralCode
import InitECandidate.Solver.Input.ReturnNormal
import InitECandidate.Solver.PanHeapGlobals

namespace InitECandidate.Solver.Mpt.AccountCopy
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Complete actual original account copy: successful allocation derives
room, and the real unrolled memcpy derives the fresh image and earlier
memory frame. A normal body spends exactly six source ticks. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (account heap : BitVec 64)
    (accountCell : source.locals.lookup (ofString "a")=some (.val (.word account)))
    (image : AccountDecode.Image source account) (earlier : account.toNat+56≤heap.toNat)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (heapAligned : heap.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    6≤source.clock ∧ heap.toNat+56≤33806089496 ∧ returned=.val (.word heap) ∧ post.clock=source.clock-6 ∧
      emptyLocalsHOLFinite post=emptyLocalsHOLFinite {source with
        globals:=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap 56#64)))
        memory:=CopyGeneral.resultMemory source.memory source.be account heap 56,clock:=source.clock-6} ∧
      (PersistentAlloc.rounded heap 56#64).toNat=heap.toNat+56 ∧ Nonempty (AccountDecode.Image post heap) ∧
      Rlp.Slices.Window source post heap.toNat (heap.toNat+56) ∧ HeapGlobals source post ∧
      post.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 56#64))) := by
  have heapLower : 2701131776≤heap.toNat := by have := image.output.lower; omega
  have argsAlloc : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [.const 56#64]=some (PersistentAlloc.values 56#64) := rfl
  rw [body_shape] at normal
  obtain ⟨room,positive,inner,tailRun,restored⟩ := PersistentAlloc.call_normal source post "b" [.const 56#64] tail heap 56#64 argsAlloc
    (PersistentAlloc.original_code source.code installed) (Input.Trap.original_code source.code installed) heapGlobal heapBound returned normal
  change heap.toNat+56≤33806089496 at room
  let allocated := PersistentAlloc.post {source with clock:=source.clock-1} heap 56#64
  let ready := bind allocated "b" heap
  have sourceCell : ready.locals.lookup (ofString "a")=some (.val (.word account)) :=
    (bind_lookup_other allocated "b" "a" heap (by decide)).trans accountCell
  have targetCell : ready.locals.lookup (ofString "b")=some (.val (.word heap)) := bind_lookup_same allocated "b" heap
  rw [tail] at tailRun
  have safe : Input.LocalPrefix (ofString "b") copyCall := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨copied,copyRun,returnRun,saved⟩ := safe.normal_continue ready inner (.return (localVar "b")) returned tailRun
  have args : evalListHOLFinite ready (h:=fun address=>Classical.propDecidable (ready.memaddrs address)) [localVar "b",localVar "a",.const 56#64]=some (CopyGeneral.values heap account 56) := by
    simp [CopyGeneral.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,sourceCell,targetCell]
  have output : AccountDecode.Output heap := ⟨heapLower,room,heapAligned⟩
  have srcArena : AllocatedBytes.Arena account 56 := ⟨image.output.lower,image.output.upper⟩
  have dstArena : AllocatedBytes.Arena heap 56 := ⟨heapLower,room⟩
  have mapped := AllocatedBytes.copy_mapped ready account heap 56 image.domain srcArena dstArena
  obtain ⟨funded,cheap,copiedEq⟩ := CopyGeneral.call_normal ready copied [localVar "b",localVar "a",.const 56#64] account heap 56 args
    (CopyGeneral.original_code source.code installed) mapped (by decide) copyRun
  have price := copy_price account heap image.output output
  rw [price] at funded
  change 5≤source.clock-1 at funded
  have actual := Input.return_normal copied inner (localVar "b") returned returnRun
  have copiedCell : copied.locals.lookup (ofString "b")=some (.val (.word heap)) := by rw [copiedEq]; exact targetCell
  have read : eval copied (localVar "b")=some (.val (.word heap)) := by simp [eval,localVar,evalHOLExact,toExact,copiedCell]
  have returnedEq : returned=.val (.word heap) := Option.some.inj (actual.1.symm.trans read)
  have postEq : post=restore source "b" (emptyLocalsHOLFinite copied) := by rw [restored,actual.2]
  have frame : emptyLocalsHOLFinite post=emptyLocalsHOLFinite {source with
      globals:=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap 56#64)))
      memory:=CopyGeneral.resultMemory source.memory source.be account heap 56,clock:=source.clock-6} := by
    rw [postEq,copiedEq]
    change emptyLocalsHOLFinite {source with globals:=_,memory:=_,clock:=source.clock-1-(CopyGeneral.cost account heap 56+1)}=_
    rw [price]
    have subtract : source.clock-1-(4+1)=source.clock-6 := by omega
    rw [subtract] <;> rfl
  have clock := congrArg PanSemStateFiniteExact.clock frame
  change post.clock=source.clock-6 at clock
  have memory := congrArg PanSemStateFiniteExact.memory frame
  change post.memory=CopyGeneral.resultMemory source.memory source.be account heap 56 at memory
  have domain := congrArg PanSemStateFiniteExact.memaddrs frame
  change post.memaddrs=source.memaddrs at domain
  have globals := congrArg PanSemStateFiniteExact.globals frame
  change post.globals=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap 56#64))) at globals
  have rounded : (PersistentAlloc.rounded heap 56#64).toNat=heap.toNat+56 := by
    rw [PersistentAlloc.rounded_nat heap 56#64 (by change heap.toNat+56+7<2^64; omega)]
    change (heap.toNat+56+7)/8*8=heap.toNat+56
    omega
  refine ⟨by omega,room,returnedEq,clock,frame,rounded,⟨copied_image source post account heap image output earlier domain memory⟩,
    copy_window source post account heap output memory,?_,?_⟩
  · intro key different
    rw [globals]
    exact HeapGlobals.update source (PersistentAlloc.rounded heap 56#64) key different
  · rw [globals]
    simp [HolFiniteMapExact.update,FUPDATE]

end InitECandidate.Solver.Mpt.AccountCopy

#print axioms InitECandidate.Solver.Mpt.AccountCopy.body_normal
