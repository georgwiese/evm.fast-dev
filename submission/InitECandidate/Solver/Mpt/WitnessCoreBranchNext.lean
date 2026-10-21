import InitECandidate.Solver.Mpt.WitnessCoreBranchPrefix
import InitECandidate.Solver.Mpt.WitnessCoreBranchAdvance
import InitECandidate.Solver.Mpt.WitnessStackRank

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Complete real continuing-child branch, from the original child store
through conditional occupancy/local-index updates and exact next-slot
state. The updated physical record satisfies occupied<=index. -/
theorem branch_children_next (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record db node child oldSlot oldMode : BitVec 64)
    (data : WitnessRecord.Description) (index : Fin 16) (occupied : Fin 17) (used : occupied.val≤index.val)
    (inside : index.val+1<16)
    (view : WitnessRecord.View source record db data) (payload : data.payload=.branch node index occupied)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word record)))
    (branchCell : source.locals.lookup (ofString "br")=some (.val (.word node)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index.val))))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word child)))
    (slotCell : source.locals.lookup (ofString "slot")=some (.val (.word oldSlot)))
    (modeCell : source.locals.lookup (ofString "mode")=some (.val (.word oldMode))) :
    let nextIndex : Fin 16:=⟨index.val+1,inside⟩
    let nextOccupied:=occupiedNext index occupied used child
    let ready:=branchCounterEntry source record node child index occupied
    let next:=advanced ready record nextIndex
    evaluateHOLFiniteState source branchChildren=(none,next) ∧
      WitnessRecord.View next record db {data with payload:=.branch node nextIndex nextOccupied} ∧
      nextOccupied.val≤nextIndex.val ∧ next.globals=source.globals ∧ next.memaddrs=source.memaddrs ∧ next.clock=source.clock := by
  let nextIndex : Fin 16:=⟨index.val+1,inside⟩
  let nextOccupied:=occupiedNext index occupied used child
  let ready:=branchCounterEntry source record node child index occupied
  let currentData:=(WitnessRecord.BranchCounter.occupied nextOccupied).description data node index occupied
  let next:=advanced ready record nextIndex
  have readyView:=branch_counter_entry_view source record db node child data index occupied used view payload
  have readyTop : ready.locals.lookup (ofString "top")=some (.val (.word record)):=
    (branch_counter_entry_local source record node child index occupied "top" (by decide)).trans topCell
  have readyIndex : ready.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 nextIndex.val))):=bind_lookup_same _ _ _
  have readySlot : ready.locals.lookup (ofString "slot")=some (.val (.word oldSlot)):=
    (branch_counter_entry_local source record node child index occupied "slot" (by decide)).trans slotCell
  have readyMode : ready.locals.lookup (ofString "mode")=some (.val (.word oldMode)):=
    (branch_counter_entry_local source record node child index occupied "mode" (by decide)).trans modeCell
  have advancedRun:=branch_advance_execute ready record db oldSlot oldMode currentData nextIndex readyView readyTop readyIndex readySlot readyMode
  have trace:=branch_children_trace source record db node child data index occupied used view payload topCell branchCell indexCell resultCell
  change evaluateHOLFiniteState source branchChildren=if index.val+1<16 then evaluateHOLFiniteState ready branchAdvance else evaluateHOLFiniteState ready branchFinish at trace
  rw [if_pos inside,advancedRun] at trace
  have currentPayload : currentData.payload=.branch node index nextOccupied:=rfl
  have nextView:=advanced_view ready record db node currentData index nextIndex nextOccupied readyView currentPayload
  have finalView : WitnessRecord.View next record db {data with payload:=.branch node nextIndex nextOccupied}:=nextView
  have readyGlobals : ready.globals=source.globals:=by unfold ready branchCounterEntry occupancyState; split <;> rfl
  have readyDomain : ready.memaddrs=source.memaddrs:=by unfold ready branchCounterEntry occupancyState; split <;> rfl
  have readyClock : ready.clock=source.clock:=by unfold ready branchCounterEntry occupancyState; split <;> rfl
  have globals : next.globals=source.globals:=readyGlobals
  have domain : next.memaddrs=source.memaddrs:=readyDomain
  have clock : next.clock=source.clock:=readyClock
  exact ⟨trace,finalView,occupied_next_bound index occupied used child,globals,domain,clock⟩

/-- The actual unchanged scratch globals in this continuing case retain
the same record allowance. Its real updated index pays the returning-to-
resolve phase change by a strict pending-frame rank decrease. -/
theorem branch_next_rank (remaining : Nat) (stack : List WitnessStackRank.Frame) (index : Fin 16) (inside : index.val+1<16) :
    WitnessStackRank.rank remaining (.branch ⟨index.val+1,inside⟩::stack) .resolve true<
      WitnessStackRank.rank remaining (.branch index::stack) .returning true :=
  WitnessStackRank.branch_next remaining stack index.val inside

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_children_next
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_next_rank
