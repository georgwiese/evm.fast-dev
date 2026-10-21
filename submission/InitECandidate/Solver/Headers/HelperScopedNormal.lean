import InitECandidate.Solver.Headers.HelperCall
import InitECandidate.Solver.Input.ScopedCallNoneData

namespace InitECandidate.Solver.Headers.Helper
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A normal scoped original helper derives its checked actual return,
genuine continuation and final lexical restoration. -/
theorem scoped_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (array pointer cursor limit control : BitVec 64) (bytes cutoff index : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (state : SliceState source pointer array cursor limit bytes cutoff items) (selected : items[index]?=some item)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some (kind.values array (BitVec.ofNat 64 index) control))
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) kind.resultShape kind.name expressions continuation)=(none,post)) :
    ∃ target value inner,Returned source target kind array pointer cursor limit bytes cutoff item.total.toNat items ∧
      shapeOfHOLExact value=kind.resultShape ∧
      evaluateHOLFiniteState (Input.CallNormal.continuationEntry source target name value) continuation=(none,inner) ∧
      post=WitnessRadix.QueryBranch.restore source name inner := by
  obtain ⟨callee,called,arrayCell,indexCell,controlCell⟩ := environment source.code.lookup kind array (BitVec.ofNat 64 index) control (original_code source.code installed kind)
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,target,value,inner,actualArgs,actualCalled,bodyRun,checked,continued,postEq⟩ :=
    Input.CallNormal.scoped_none_data source post name kind.resultShape kind.name expressions continuation normal
  have valuesEq : actualValues=kind.values array (BitVec.ofNat 64 index) control := Option.some.inj (actualArgs.symm.trans args)
  rw [valuesEq] at actualCalled
  have same:=Option.some.inj (called.symm.trans actualCalled)
  simp only [Prod.mk.injEq] at same
  obtain ⟨bodyEq,calleeEq,shapeEq⟩ := same
  subst actualBody
  subst actualCallee
  subst actualShape
  let entry:=callEntryStateHOLFinite source callee
  have ready:=entry_state source callee array pointer cursor limit bytes cutoff items state
  obtain ⟨next,globals⟩ := body_normal_state entry target kind array pointer cursor limit control bytes cutoff index items item ready selected arrayCell indexCell controlCell installed value bodyRun
  have fields:=Input.evaluation_fields entry target kind.body (some (.returned value)) bodyRun
  have price:=body_cost entry kind array pointer cursor limit control bytes cutoff index items item ready selected arrayCell indexCell controlCell installed
  have clock:=evaluateHOLFiniteState_clock_le entry kind.body
  rw [bodyRun] at clock price
  have shape : shapeOfHOLExact value=kind.resultShape := (shapeEqHOL_eq_true _ _).mp (Bool.and_eq_true_iff.mp checked).1
  have entryClock : entry.clock=source.clock-1 := rfl
  refine ⟨target,value,inner,⟨next,globals,fields.2.2.2,fields.1,fields.2.1,fields.2.2.1,?_,?_⟩,shape,continued,postEq⟩
  · change target.clock≤entry.clock at clock
    rw [entryClock] at clock
    omega
  · change entry.clock-target.clock≤kind.bodyPrice item.total.toNat at price
    rw [entryClock] at price
    change target.clock≤entry.clock at clock
    rw [entryClock] at clock
    omega

end InitECandidate.Solver.Headers.Helper

#print axioms InitECandidate.Solver.Headers.Helper.scoped_normal
