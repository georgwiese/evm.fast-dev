import InitECandidate.Solver.Headers.CurrentHelpers.Call

namespace InitECandidate.Solver.Headers.CurrentHelpers
open Helper
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

theorem scoped_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (array pointer control : BitVec 64) (bytes index : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (state : SliceImage source pointer array bytes items) (selected : items[index]?=some item)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some (kind.values array (BitVec.ofNat 64 index) control))
    (finalValue : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) kind.resultShape kind.name expressions continuation)=(some (.returned finalValue),post)) :
    ∃ target value inner,Returned source target kind item.total.toNat ∧ shapeOfHOLExact value=kind.resultShape ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source target name value) continuation=(some (.returned finalValue),inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called,arrayCell,indexCell,controlCell⟩:=environment source.code.lookup kind array (BitVec.ofNat 64 index) control (original_code source.code state.arena.code kind)
  let entry:=callEntryStateHOLFinite source callee
  have ready : SliceImage entry pointer array bytes items := state.of_frame rfl
  obtain ⟨funded,target,value,inner,bodyRun,checked,continued,endpoint⟩:=CallNormal.scoped_normal source post name kind.resultShape kind.name expressions _ kind.body continuation callee kind.resultShape args called finalValue run
  have frame:=body_frame entry target kind array pointer control bytes index items item ready selected arrayCell indexCell controlCell value bodyRun
  have shape:=(shapeEqHOL_eq_true _ _).mp (Bool.and_eq_true_iff.mp checked).1
  have price:=body_cost entry kind array pointer control bytes index items item ready selected arrayCell indexCell controlCell state.arena.code
  have forward:=evaluateHOLFiniteState_clock_le entry kind.body
  rw [bodyRun] at price forward
  change source.clock-1-target.clock≤bodyPrice kind item.total.toNat at price
  change target.clock≤source.clock-1 at forward
  exact ⟨target,value,inner,⟨frame,(by omega),(by omega)⟩,shape,continued,endpoint⟩

end InitECandidate.Solver.Headers.CurrentHelpers

#print axioms InitECandidate.Solver.Headers.CurrentHelpers.scoped_returned
