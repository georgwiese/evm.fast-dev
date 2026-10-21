import InitECandidate.Solver.Mpt.WitnessCoreBranchValueNormal
import InitECandidate.Solver.Mpt.WitnessCoreBranchFinishNormal
import InitECandidate.Solver.Input.ScopeLookup

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def branchFinishedState (source built : PanSemStateFiniteExact 64 Guest.HostMemory) (node previous : BitVec 64)
    (data : WitnessRecord.Description) (header bytes flag : BitVec 64) (occupied : Fin 17) :=
  let arrayReady:=QueryBranch.bind source "arr2" data.array
  let answer:=Rlp.Item.result (Rlp.Slices.itemPointer data.listPointer data.items 16) header bytes flag
  let parsed:=Input.CallNormal.continuationEntry arrayReady built "bv" answer
  let entered:=QueryBranch.bind parsed "occ" (BitVec.ofNat 64 occupied.val)
  let valued:=branchValueState entered node (Rlp.Slices.itemPointer data.listPointer data.items 16) header bytes flag occupied
  restore source "arr2" (restore arrayReady "bv" (restore parsed "occ" (metadataState valued node data.pointer data.length previous)))

/-- Complete unchanged final-child arr2/parser/value/guard/metadata/pop
normal contract. The item and every resumed state come from the genuine
execution; no future parse success or occupancy-guard success is assumed. -/
theorem branch_finish_pop_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db node previous child heap cursor limit : BitVec 64) (data : WitnessRecord.Description)
    (index : Fin 16) (occupied : Fin 17)
    (view : WitnessRecord.View source record db data) (payload : data.payload=.branch node index occupied)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word record)))
    (branchCell : source.locals.lookup (ofString "br")=some (.val (.word node)))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word child)))
    (previousCell : source.memory record=.word previous)
    (arena : Rlp.Validation.Arena source cursor limit) (before : data.BeforeHeap heap.toNat)
    (recordAbove : cursor.toNat≤record.toNat) (below : cursor.toNat≤2713717616) (heapLower : 2713731432≤heap.toNat)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source branchFinish=(none,post)) :
    ∃ item : Rlp.ListItem, ∃ built header bytes flag,
      data.items[16]?=some item ∧
      Rlp.Item.Valid (Rlp.Slices.itemPointer data.listPointer data.items 16) item.total.toNat
        (Rlp.Item.result (Rlp.Slices.itemPointer data.listPointer data.items 16) header bytes flag) ∧
      2≤branchValueOccupied bytes flag occupied ∧ branchValueOccupied bytes flag occupied≤17 ∧
      Rlp.Validation.Arena post cursor limit ∧
      (∀ key,post.globals.lookup key=source.globals.lookup key) ∧ post.memaddrs=source.memaddrs ∧ post.be=source.be ∧ post.code=source.code ∧
      post=branchFinishedState source built node previous data header bytes flag occupied ∧ Rlp.Validation.Above source built cursor.toNat := by
  obtain ⟨item,built,header,bytes,flag,inner,selected,valid,readyView,readyArena,above,domain,endian,code,globals,valueCell,continued,endpoint⟩:=
    branch_finish_normal source post record db node heap cursor limit data index occupied view payload topCell arena before recordAbove below heapLower installed normal
  let arrayReady:=QueryBranch.bind source "arr2" data.array
  let answer:=Rlp.Item.result (Rlp.Slices.itemPointer data.listPointer data.items 16) header bytes flag
  let ready:=Input.CallNormal.continuationEntry arrayReady built "bv" answer
  have readyTop : ready.locals.lookup (ofString "top")=some (.val (.word record)):=
    (Input.CallNormal.continuation_lookup_other arrayReady built "bv" "top" answer (by decide)).trans
      ((bind_lookup_other source "arr2" "top" _ (by decide)).trans topCell)
  have readyBranch : ready.locals.lookup (ofString "br")=some (.val (.word node)):=
    (Input.CallNormal.continuation_lookup_other arrayReady built "bv" "br" answer (by decide)).trans
      ((bind_lookup_other source "arr2" "br" _ (by decide)).trans branchCell)
  have readyResult : ready.locals.lookup (ofString "result")=some (.val (.word child)):=
    (Input.CallNormal.continuation_lookup_other arrayReady built "bv" "result" answer (by decide)).trans
      ((bind_lookup_other source "arr2" "result" _ (by decide)).trans resultCell)
  have readyPrevious : ready.memory record=.word previous:=(above record recordAbove).trans previousCell
  have readyInstalled : Input.OriginalCode.Installed ready.code:=by change Input.OriginalCode.Installed ready.code; rw [code]; exact installed
  obtain ⟨enough,innerEq⟩:=after_branch_value_normal ready inner record db node previous child
    (Rlp.Slices.itemPointer data.listPointer data.items 16) header bytes flag data index occupied readyView payload readyTop readyBranch readyResult valueCell readyPrevious readyInstalled continued
  have postEq : post=branchFinishedState source built node previous data header bytes flag occupied:=by
    rw [endpoint,innerEq]
    rfl
  have postGlobals (key : MlS) : post.globals.lookup key=source.globals.lookup key:=by
    rw [postEq]
    change (branchValueState (QueryBranch.bind ready "occ" (BitVec.ofNat 64 occupied.val)) node
      (Rlp.Slices.itemPointer data.listPointer data.items 16) header bytes flag occupied).globals.lookup key=source.globals.lookup key
    have same:=(branch_value_state_fields (QueryBranch.bind ready "occ" (BitVec.ofNat 64 occupied.val)) node
      (Rlp.Slices.itemPointer data.listPointer data.items 16) header bytes flag occupied (bind_lookup_same _ _ _)).2.1
    rw [same]
    exact globals key
  have postDomain : post.memaddrs=source.memaddrs:=by
    rw [postEq]
    change (branchValueState (QueryBranch.bind ready "occ" (BitVec.ofNat 64 occupied.val)) node
      (Rlp.Slices.itemPointer data.listPointer data.items 16) header bytes flag occupied).memaddrs=source.memaddrs
    exact ((branch_value_state_fields _ _ _ _ _ _ _ (bind_lookup_same _ _ _)).2.2.1).trans domain
  have postEndian : post.be=source.be:=by
    rw [postEq]
    unfold branchFinishedState branchValueState
    split
    · split <;> exact endian
    · exact endian
  have postCode : post.code=source.code:=by
    rw [postEq]
    unfold branchFinishedState branchValueState
    split
    · split <;> exact code
    · exact code
  have postArena : Rlp.Validation.Arena post cursor limit:=
    ⟨postDomain.trans arena.domain,(postGlobals _).trans arena.cursorGlobal,(postGlobals _).trans arena.limitGlobal,
      arena.ordered,arena.aligned,arena.lower,arena.upper⟩
  exact ⟨item,built,header,bytes,flag,selected,valid,enough,branch_value_occupied_bound bytes flag occupied,postArena,postGlobals,postDomain,postEndian,postCode,postEq,above⟩

theorem branch_finished_fields (source built : PanSemStateFiniteExact 64 Guest.HostMemory) (node previous : BitVec 64)
    (data : WitnessRecord.Description) (header bytes flag : BitVec 64) (occupied : Fin 17) :
    let post:=branchFinishedState source built node previous data header bytes flag occupied
    post.locals.lookup (ofString "top")=some (.val (.word previous)) ∧
      post.locals.lookup (ofString "result")=some (.val (.word node)) := by
  dsimp only [branchFinishedState]
  rw [Input.ScalarScope.restore_other _ _ "arr2" "top" (by decide),Input.ScalarScope.restore_other _ _ "arr2" "result" (by decide),
    Input.ScalarScope.restore_other _ _ "bv" "top" (by decide),Input.ScalarScope.restore_other _ _ "bv" "result" (by decide),
    Input.ScalarScope.restore_other _ _ "occ" "top" (by decide),Input.ScalarScope.restore_other _ _ "occ" "result" (by decide)]
  exact ⟨(metadata_fields _ _ _ _ _).1,(metadata_fields _ _ _ _ _).2.1⟩

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_finish_pop_normal
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_finished_fields
