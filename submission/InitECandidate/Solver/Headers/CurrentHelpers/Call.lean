import InitECandidate.Solver.Headers.CurrentHelpers.Frame
import InitECandidate.Solver.Input.ScopedCallTrace
import InitECandidate.Solver.Input.AssignedCallData

namespace InitECandidate.Solver.Headers.CurrentHelpers
open Helper
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

/-- Every assigned/ignored caller is priced from its actual selected row. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (array pointer control : BitVec 64) (bytes index : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (state : SliceImage source pointer array bytes items) (selected : items[index]?=some item)
    (destination : Option (Option MlS)) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some (kind.values array (BitVec.ofNat 64 index) control)) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) kind.name expressions)).2.clock≤bodyPrice kind item.total.toNat+1 := by
  obtain ⟨callee,called,arrayCell,indexCell,controlCell⟩:=environment source.code.lookup kind array (BitVec.ofNat 64 index) control (original_code source.code state.arena.code kind)
  have ready : SliceImage (callEntryStateHOLFinite source callee) pointer array bytes items := state.of_frame rfl
  have price:=body_cost (callEntryStateHOLFinite source callee) kind array pointer control bytes index items item ready selected arrayCell indexCell controlCell state.arena.code
  exact ClockCost.call_current source destination kind.name expressions _ kind.body callee kind.resultShape (bodyPrice kind item.total.toNat) args called price

structure Returned (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (rowBytes : Nat) : Prop where
  frame : LocalEffects.erase target=LocalEffects.erase source
  forward : target.clock≤source.clock
  cost : source.clock-target.clock≤bodyPrice kind rowBytes+1

/-- Price every stopped outcome or retain a genuine typed return, full
nonlocal frame and real continuation before charging its suffix. -/
theorem scoped_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (array pointer control : BitVec 64) (bytes index : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (state : SliceImage source pointer array bytes items) (selected : items[index]?=some item)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some (kind.values array (BitVec.ofNat 64 index) control))
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) kind.resultShape kind.name expressions continuation)=(result,post)) :
    source.clock-post.clock≤bodyPrice kind item.total.toNat+1 ∨
      ∃ target value inner,Returned source target kind item.total.toNat ∧ shapeOfHOLExact value=kind.resultShape ∧
        evaluateHOLFiniteState (CallNormal.continuationEntry source target name value) continuation=(result,inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called,arrayCell,indexCell,controlCell⟩:=environment source.code.lookup kind array (BitVec.ofNat 64 index) control (original_code source.code state.arena.code kind)
  let entry:=callEntryStateHOLFinite source callee
  have ready : SliceImage entry pointer array bytes items := state.of_frame rfl
  have price:=body_cost entry kind array pointer control bytes index items item ready selected arrayCell indexCell controlCell state.arena.code
  rcases CallNormal.scoped_trace source post name kind.resultShape kind.name expressions _ kind.body continuation callee kind.resultShape (bodyPrice kind item.total.toNat) args called price result run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨target,value,inner,funded,bodyRun,checked,forward,cost,continued,endpoint⟩:=reached
    have frame:=body_frame entry target kind array pointer control bytes index items item ready selected arrayCell indexCell controlCell value bodyRun
    have shape:=(shapeEqHOL_eq_true _ _).mp (Bool.and_eq_true_iff.mp checked).1
    exact Or.inr ⟨target,value,inner,⟨frame,forward,cost⟩,shape,continued,endpoint⟩

/-- Actual assigned calls supply the checked new local value and preserve
all nonlocal data; the destination's validity comes from its real execution. -/
theorem assigned_none (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (array pointer control : BitVec 64) (bytes index : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (state : SliceImage source pointer array bytes items) (selected : items[index]?=some item)
    (name : MlS) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some (kind.values array (BitVec.ofNat 64 index) control))
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,name),none)) kind.name expressions)=(none,post)) :
    ∃ value : ValueHOL 64,shapeOfHOLExact value=kind.resultShape ∧ LocalEffects.erase post=LocalEffects.erase source ∧
      post.locals=(source.locals.update (name,value)) := by
  obtain ⟨callee,called,arrayCell,indexCell,controlCell⟩:=environment source.code.lookup kind array (BitVec.ofNat 64 index) control (original_code source.code state.arena.code kind)
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,target,value,actualArgs,actualCalled,bodyRun,checked,endpoint⟩:=CallNormal.local_data source post name kind.name expressions normal
  have valuesEq:=Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  have entryEq:=Option.some.inj (actualCalled.symm.trans called)
  cases entryEq
  have ready : SliceImage (callEntryStateHOLFinite source callee) pointer array bytes items := state.of_frame rfl
  have frame:=body_frame (callEntryStateHOLFinite source callee) target kind array pointer control bytes index items item ready selected arrayCell indexCell controlCell value bodyRun
  refine ⟨value,(shapeEqHOL_eq_true _ _).mp checked,?_,?_⟩
  · rw [endpoint]; exact frame
  · rw [endpoint]; rfl

/-- A real normal scoped caller must reach its genuine checked callee return;
it retains the exact continuation rather than using a small-cost alternative. -/
theorem scoped_none (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (array pointer control : BitVec 64) (bytes index : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (state : SliceImage source pointer array bytes items) (selected : items[index]?=some item)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some (kind.values array (BitVec.ofNat 64 index) control))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) kind.resultShape kind.name expressions continuation)=(none,post)) :
    ∃ target value inner,Returned source target kind item.total.toNat ∧ shapeOfHOLExact value=kind.resultShape ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source target name value) continuation=(none,inner) ∧ post=restore source name inner := by
  obtain ⟨callee,called,arrayCell,indexCell,controlCell⟩:=environment source.code.lookup kind array (BitVec.ofNat 64 index) control (original_code source.code state.arena.code kind)
  let entry:=callEntryStateHOLFinite source callee
  have ready : SliceImage entry pointer array bytes items := state.of_frame rfl
  obtain ⟨funded,target,value,inner,bodyRun,checked,continued,endpoint⟩:=CallNormal.scoped_none source post name kind.resultShape kind.name expressions _ kind.body continuation callee kind.resultShape args called run
  have frame:=body_frame entry target kind array pointer control bytes index items item ready selected arrayCell indexCell controlCell value bodyRun
  have shape:=(shapeEqHOL_eq_true _ _).mp (Bool.and_eq_true_iff.mp checked).1
  have price:=body_cost entry kind array pointer control bytes index items item ready selected arrayCell indexCell controlCell state.arena.code
  have forward:=evaluateHOLFiniteState_clock_le entry kind.body
  rw [bodyRun] at price forward
  change source.clock-1-target.clock≤bodyPrice kind item.total.toNat at price
  change target.clock≤source.clock-1 at forward
  exact ⟨target,value,inner,⟨frame,(by omega),(by omega)⟩,shape,continued,endpoint⟩

end InitECandidate.Solver.Headers.CurrentHelpers

#print axioms InitECandidate.Solver.Headers.CurrentHelpers.call_cost
#print axioms InitECandidate.Solver.Headers.CurrentHelpers.scoped_trace
#print axioms InitECandidate.Solver.Headers.CurrentHelpers.assigned_none

#print axioms InitECandidate.Solver.Headers.CurrentHelpers.scoped_none
