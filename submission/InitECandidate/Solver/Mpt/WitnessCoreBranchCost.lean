import InitECandidate.Solver.Mpt.WitnessCoreBranchPrefix
import InitECandidate.Solver.Mpt.WitnessCoreBranchValueRows
import InitECandidate.Solver.Input.ClockCostCurrent

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- All outcomes of the genuine original child update and subsequent
choice fit the final-value allowance. Continuing to another child spends
no source ticks; the last child pays the actual bounded row16 parser. -/
theorem branch_children_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db node child cursor limit : BitVec 64) (data : WitnessRecord.Description)
    (index : Fin 16) (occupied : Fin 17) (used : occupied.val≤index.val)
    (view : WitnessRecord.View source record db data) (payload : data.payload=.branch node index occupied)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word record)))
    (branchCell : source.locals.lookup (ofString "br")=some (.val (.word node)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index.val))))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word child)))
    (arena : Rlp.Validation.Arena source cursor limit) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source branchChildren).2.clock≤60*data.bytes+43 := by
  let ready:=branchCounterEntry source record node child index occupied
  let nextOccupied:=occupiedNext index occupied used child
  let currentData:=(WitnessRecord.BranchCounter.occupied nextOccupied).description data node index occupied
  have trace:=branch_children_trace source record db node child data index occupied used view payload topCell branchCell indexCell resultCell
  change evaluateHOLFiniteState source branchChildren=if index.val+1<16 then evaluateHOLFiniteState ready branchAdvance else evaluateHOLFiniteState ready branchFinish at trace
  have clock : ready.clock=source.clock:=by unfold ready branchCounterEntry occupancyState; split <;> rfl
  rw [trace]
  by_cases inside : index.val+1<16
  · rw [if_pos inside,(branch_advance_quiet ready.code) ready rfl,clock]
    omega
  · rw [if_neg inside,←clock]
    have readyView:=branch_counter_entry_view source record db node child data index occupied used view payload
    have readyTop : ready.locals.lookup (ofString "top")=some (.val (.word record)):=
      (branch_counter_entry_local source record node child index occupied "top" (by decide)).trans topCell
    have globals : ready.globals=source.globals:=by unfold ready branchCounterEntry occupancyState; split <;> rfl
    have domain : ready.memaddrs=source.memaddrs:=by unfold ready branchCounterEntry occupancyState; split <;> rfl
    have code : ready.code=source.code:=by unfold ready branchCounterEntry occupancyState; split <;> rfl
    have readyArena:=arena.of_fields source ready cursor limit domain globals
    have readyInstalled : Input.OriginalCode.Installed ready.code:=by rw [code]; exact installed
    exact branch_finish_cost ready record db node cursor limit currentData index nextOccupied readyView rfl readyTop readyArena readyInstalled

/-- The actual br/i record loads and their declarations compose with
the complete child branch bound; no callee result or future success is
required, and arbitrary traps or parser failure are priced as well. -/
theorem return_branch_node_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db node child cursor limit : BitVec 64) (data : WitnessRecord.Description)
    (index : Fin 16) (occupied : Fin 17) (used : occupied.val≤index.val)
    (view : WitnessRecord.View source record db data) (payload : data.payload=.branch node index occupied)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word record)))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word child)))
    (arena : Rlp.Validation.Arena source cursor limit) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source returnBranchNode).2.clock≤60*data.bytes+43 := by
  have mapped16 : source.memaddrs (record+16#64):=by simpa only [byteAddress] using view.mapped source record db data 16 (by decide) (by decide)
  have mapped32 : source.memaddrs (record+32#64):=by simpa only [byteAddress] using view.mapped source record db data 32 (by decide) (by decide)
  have nodeCell : source.memory (record+16#64)=.word node:=view.cells (16,node) (by simp [WitnessRecord.Description.cells,payload])
  have indexCell : source.memory (record+32#64)=.word (BitVec.ofNat 64 index.val):=view.cells (32,BitVec.ofNat 64 index.val) (by simp [WitnessRecord.Description.cells,payload])
  have nodeRead : eval source (readAt "top" 16#64)=some (.val (.word node)):=by
    simp [eval,readAt,evalHOLExact,evalListHOLExact,localVar,toExact,topCell,valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,mapped16,nodeCell]
  let branchReady:=QueryBranch.bind source "br" node
  let ready:=QueryBranch.bind branchReady "i" (BitVec.ofNat 64 index.val)
  have branchTop : branchReady.locals.lookup (ofString "top")=some (.val (.word record)):=
    (bind_lookup_other source "br" "top" node (by decide)).trans topCell
  have indexRead : eval branchReady (readAt "top" 32#64)=some (.val (.word (BitVec.ofNat 64 index.val))):=by
    simp [eval,readAt,evalHOLExact,evalListHOLExact,localVar,toExact,branchTop,valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,mapped32,indexCell]
    exact ⟨mapped32,indexCell⟩
  have readyTop : ready.locals.lookup (ofString "top")=some (.val (.word record)):=
    (bind_lookup_other branchReady "i" "top" _ (by decide)).trans branchTop
  have readyBranch : ready.locals.lookup (ofString "br")=some (.val (.word node)):=
    (bind_lookup_other branchReady "i" "br" _ (by decide)).trans (bind_lookup_same _ _ _)
  have readyResult : ready.locals.lookup (ofString "result")=some (.val (.word child)):=
    (bind_lookup_other branchReady "i" "result" _ (by decide)).trans
      ((bind_lookup_other source "br" "result" node (by decide)).trans resultCell)
  have priced:=branch_children_cost ready record db node child cursor limit data index occupied used
    (view.of_fields source ready record db data rfl rfl) payload readyTop readyBranch (bind_lookup_same _ _ _) readyResult
    (arena.of_fields source ready cursor limit rfl rfl) installed
  have innerPrice:=Input.ClockCost.declared_current branchReady "i" (readAt "top" 32#64) (BitVec.ofNat 64 index.val) branchChildren
    (60*data.bytes+43) indexRead priced
  rw [←branch_index_read_shape] at innerPrice
  rw [return_branch_node_shape]
  exact Input.ClockCost.declared_current source "br" (readAt "top" 16#64) node branchIndexRead (60*data.bytes+43) nodeRead innerPrice

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_children_cost
#print axioms InitECandidate.Solver.Mpt.WitnessCore.return_branch_node_cost
