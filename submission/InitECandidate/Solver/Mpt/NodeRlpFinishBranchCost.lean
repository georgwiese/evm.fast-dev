import InitECandidate.Solver.Mpt.NodeRlpFinishScanNormal
import InitECandidate.Solver.Mpt.ValueEncodedLenCall
import InitECandidate.Solver.Mpt.TrieWalkValueAgreement

namespace InitECandidate.Solver.Mpt.NodeRlpFinish
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem value_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64) (limit : Nat)
    (property : BitVec 64→BitVec 64→Prop) (view : TrieWalk.ValueView source.memory source.memaddrs node 160#64 168#64 limit property)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) valueArguments=some [.val (.word view.pointer),.val (.word view.length)] := by
  simp [valueArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,nodeCell,valueIsWord,valueWord,wordOpHOL,wordOp,
    memLoadHOLExact,isWfShapeExactHOL,view.pointerMapped,view.pointerStored,view.lengthMapped,view.lengthStored]

theorem after_scan_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64) (limit : Nat)
    (property : BitVec 64→BitVec 64→Prop) (view : TrieWalk.ValueView source.memory source.memaddrs node 160#64 168#64 limit property)
    (fits : limit+9<2^64) (installed : Input.OriginalCode.Installed source.code)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node))) :
    source.clock-(evaluateHOLFiniteState source afterScan).2.clock≤12 := by
  obtain ⟨callee,called,_pCell,nCell⟩:=ValueEncodedLen.environment source.code.lookup view.pointer view.length (ValueEncodedLen.original_code source.code installed)
  have price:=ValueEncodedLen.body_cost (callEntryStateHOLFinite source callee) view.length (by have size:=view.payload.1; omega) installed nCell
  rw [after_scan_shape]
  exact Input.ClockCost.scoped_current source (ofString "vl2") .one (ofString "rlp_value_encoded_len") valueArguments _ ValueEncodedLen.body addValue callee .one 11 0
    (value_arguments source node limit property view nodeCell) called price (Input.ClockCost.assign source.code _ _)

/-- The literal original258 branch payload phase costs at most60 source
ticks: at most48 for its16child scan and12 for its real value-size call.
Actual scan frames derive the continuation's readable node/value facts. -/
theorem branch_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64) (limit : Nat)
    (property : BitVec 64→BitVec 64→Prop) (view : TrieWalk.ValueView source.memory source.memaddrs node 160#64 168#64 limit property)
    (fits : limit+9<2^64) (installed : Input.OriginalCode.Installed source.code)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (tagCell : source.locals.lookup (ofString "k")=some (.val (.word 3#64))) :
    source.clock-(evaluateHOLFiniteState source branchChoice).2.clock≤60 := by
  let entered:=bind source "i" 0#64
  have enteredNode : entered.locals.lookup (ofString "node")=some (.val (.word node)):=
    (bind_lookup_other source "i" "node" 0#64 (by decide)).trans nodeCell
  have suffix (current : PanSemStateFiniteExact 64 Guest.HostMemory) (run : evaluateHOLFiniteState entered scanLoop=(none,current)) :
      current.clock-(evaluateHOLFiniteState current afterScan).2.clock≤12:=by
    have frame:=Input.LocalEffects.loop source.code scanTest scanBody (scan_body_readonly source.code installed) entered rfl
    rw [←scan_shapes.1,run] at frame
    have memory:=Input.LocalEffects.memory_of_erase entered current frame
    have domain:=congrArg PanSemStateFiniteExact.memaddrs frame
    have codes:=Input.LocalEffects.code_of_erase entered current frame
    have currentView:=view.of_agreement source.memory current.memory source.memaddrs current.memaddrs node 160#64 168#64 limit domain (congrFun memory _) (congrFun memory _)
    have saved:=(Input.LocalPrefix.loop scanTest scan_body_safe).summary_full entered
    unfold Input.LocalSummary at saved
    rw [←scan_shapes.1,run] at saved
    exact after_scan_cost current node limit property currentView fits (by rw [codes]; exact installed) ((saved.1 rfl).trans enteredNode)
  have price:=Input.ClockCost.sequence_reached_current entered scanLoop afterScan 48 12 (by
    have cost:=scan_cost entered 0#64 installed (bind_lookup_same _ _ _) (by decide)
    exact cost) suffix
  have selected : evaluateHOLFiniteState source branchChoice=evaluateHOLFiniteState source (.dec (ofString "i") .one (.const 0#64) (.seq scanLoop afterScan)):=by
    rw [scan_shapes.2.2,evaluateHOLFiniteState_ite]
    simp [evalHOLExact,toExact,localVar,tagCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [selected]
  exact Input.ClockCost.declared_current source "i" (.const 0#64) 0#64 (.seq scanLoop afterScan) 60 rfl price

end InitECandidate.Solver.Mpt.NodeRlpFinish

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.value_arguments
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.after_scan_cost
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.branch_cost
