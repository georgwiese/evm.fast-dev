import InitECandidate.Solver.Mpt.WitnessCoreBranchPrefix
import InitECandidate.Solver.Mpt.WitnessCoreBranchPopNormal

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Complete final-child transition from the actual child store through
OCC/i updates, real row16 parsing, value writes, guard and parent pop. -/
theorem branch_children_last_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db node previous child heap cursor limit : BitVec 64) (data : WitnessRecord.Description)
    (index : Fin 16) (occupied : Fin 17) (used : occupied.val≤index.val) (last : ¬index.val+1<16)
    (view : WitnessRecord.View source record db data) (payload : data.payload=.branch node index occupied)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word record)))
    (branchCell : source.locals.lookup (ofString "br")=some (.val (.word node)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index.val))))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word child)))
    (previousCell : source.memory record=.word previous)
    (live : Rlp.LiveArena source) (arena : Rlp.Validation.Arena source cursor limit) (before : data.BeforeHeap heap.toNat)
    (recordAbove : cursor.toNat≤record.toNat)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source branchChildren=(none,post)) :
    let ready:=branchCounterEntry source record node child index occupied
    let nextOccupied:=occupiedNext index occupied used child
    let currentData:=(WitnessRecord.BranchCounter.occupied nextOccupied).description data node index occupied
    ∃ item : Rlp.ListItem, ∃ built header bytes flag,
      data.items[16]?=some item ∧
      Rlp.Item.Valid (Rlp.Slices.itemPointer data.listPointer data.items 16) item.total.toNat
        (Rlp.Item.result (Rlp.Slices.itemPointer data.listPointer data.items 16) header bytes flag) ∧
      2≤branchValueOccupied bytes flag nextOccupied ∧ branchValueOccupied bytes flag nextOccupied≤17 ∧
      Rlp.Validation.Arena post cursor limit ∧
      (∀ key,post.globals.lookup key=source.globals.lookup key) ∧ post.memaddrs=source.memaddrs ∧ post.be=source.be ∧ post.code=source.code ∧
      post=branchFinishedState ready built node previous currentData header bytes flag nextOccupied ∧ Rlp.Validation.Above ready built cursor.toNat ∧ Rlp.CurrentItem.Frame ready built := by
  let ready:=branchCounterEntry source record node child index occupied
  let nextOccupied:=occupiedNext index occupied used child
  let currentData:=(WitnessRecord.BranchCounter.occupied nextOccupied).description data node index occupied
  have trace:=branch_children_trace source record db node child data index occupied used view payload topCell branchCell indexCell resultCell
  change evaluateHOLFiniteState source branchChildren=if index.val+1<16 then evaluateHOLFiniteState ready branchAdvance else evaluateHOLFiniteState ready branchFinish at trace
  rw [if_neg last,normal] at trace
  have finishRun : evaluateHOLFiniteState ready branchFinish=(none,post):=trace.symm
  have readyView:=branch_counter_entry_view source record db node child data index occupied used view payload
  have readyPayload : currentData.payload=.branch node index nextOccupied:=rfl
  have readyTop : ready.locals.lookup (ofString "top")=some (.val (.word record)):=
    (branch_counter_entry_local source record node child index occupied "top" (by decide)).trans topCell
  have readyBranch : ready.locals.lookup (ofString "br")=some (.val (.word node)):=
    (branch_counter_entry_local source record node child index occupied "br" (by decide)).trans branchCell
  have readyResult : ready.locals.lookup (ofString "result")=some (.val (.word child)):=
    (branch_counter_entry_local source record node child index occupied "result" (by decide)).trans resultCell
  have readyGlobals : ready.globals=source.globals:=by unfold ready branchCounterEntry occupancyState; split <;> rfl
  have readyDomain : ready.memaddrs=source.memaddrs:=by unfold ready branchCounterEntry occupancyState; split <;> rfl
  have readyEndian : ready.be=source.be:=by unfold ready branchCounterEntry occupancyState; split <;> rfl
  have readyCode : ready.code=source.code:=by unfold ready branchCounterEntry occupancyState; split <;> rfl
  have readyArena:=arena.of_fields source ready cursor limit readyDomain readyGlobals
  have readyBefore:=WitnessRecord.BranchCounter.before_heap (.occupied nextOccupied) data node index occupied heap.toNat payload before
  have owned:=view.owned
  simp only [payload,WitnessRecord.Payload.Owned] at owned
  have nodeBeforeRecord : node.toNat+176≤record.toNat:=by simpa only [payload,WitnessRecord.Payload.endAddress] using view.payload_before_record source record db data
  have recordUpper:=view.ceiling
  have nodeUpper:=owned.1.upper
  have indexBound:=index.isLt
  have childNumber : (WitnessRecord.childAddress node index).toNat=node.toNat+(32+8*index.val):=
    byteAddress_toNat node (32+8*index.val) (by omega)
  have recordNumber : (record+40#64).toNat=record.toNat+40:=byteAddress_toNat record 40 (by omega)
  have awayChild : record≠WitnessRecord.childAddress node index:=by intro same; have number:=congrArg BitVec.toNat same; rw [childNumber] at number; omega
  have awayOccupied : record≠record+40#64:=by intro same; have number:=congrArg BitVec.toNat same; rw [recordNumber] at number; omega
  have readyPrevious : ready.memory record=.word previous:=
    (branch_counter_entry_memory source record node child index occupied record awayChild awayOccupied).trans previousCell
  have readyInstalled : Input.OriginalCode.Installed ready.code:=by rw [readyCode]; exact installed
  obtain ⟨item,built,header,bytes,flag,selected,valid,enough,upper,postArena,globals,domain,endian,code,endpoint,above,frame⟩:=
    branch_finish_pop_normal ready post record db node previous child heap cursor limit currentData index nextOccupied readyView readyPayload
      readyTop readyBranch readyResult readyPrevious (live.of_cursors readyDomain readyCode (by rw [readyGlobals]) (by rw [readyGlobals])) readyArena readyBefore recordAbove readyInstalled finishRun
  exact ⟨item,built,header,bytes,flag,selected,valid,enough,upper,postArena,
    fun key=>(globals key).trans (congrArg (fun cells=>cells.lookup key) readyGlobals),domain.trans readyDomain,endian.trans readyEndian,code.trans readyCode,endpoint,above,frame⟩

theorem branch_last_rank (remaining : Nat) (stack : List WitnessStackRank.Frame) (index : Fin 16) :
    WitnessStackRank.rank remaining stack .returning true<
      WitnessStackRank.rank remaining (.branch index::stack) .returning true :=
  WitnessStackRank.pop remaining stack (.branch index)

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_children_last_normal
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_last_rank
