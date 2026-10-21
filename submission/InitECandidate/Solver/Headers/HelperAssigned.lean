import InitECandidate.Solver.Headers.HelperCall
import InitECandidate.Solver.Input.AssignedCallData

namespace InitECandidate.Solver.Headers.Helper
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A real normal assignment from an original field helper derives its
actual checked return and exact caller-local update. The existing binding's
validity is established by the observed call, rather than assumed. -/
theorem assigned_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (array pointer cursor limit control : BitVec 64) (bytes cutoff index : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (state : SliceState source pointer array cursor limit bytes cutoff items) (selected : items[index]?=some item)
    (name : String) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some (kind.values array (BitVec.ofNat 64 index) control))
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,ofString name),none)) kind.name expressions)=(none,post)) :
    ∃ target value,Returned source target kind array pointer cursor limit bytes cutoff item.total.toNat items ∧
      shapeOfHOLExact value=kind.resultShape ∧ post=Input.CallNormal.continuationEntry source target name value := by
  obtain ⟨callee,called,arrayCell,indexCell,controlCell⟩ := environment source.code.lookup kind array (BitVec.ofNat 64 index) control (original_code source.code installed kind)
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,target,value,actualArgs,actualCalled,bodyRun,checked,postEq⟩ :=
    Input.CallNormal.local_data source post (ofString name) kind.name expressions normal
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
  have price:=call_cost source kind array pointer cursor limit control bytes cutoff index items item state selected (some (some (ofString name))) expressions args installed
  change source.clock-(evaluateHOLFiniteState source (.call (some (some (.local,ofString name),none)) kind.name expressions)).2.clock≤_ at price
  rw [normal] at price
  have clock:=evaluateHOLFiniteState_clock_le source (.call (some (some (.local,ofString name),none)) kind.name expressions)
  rw [normal] at clock
  have postClock : post.clock=target.clock := by rw [postEq]; rfl
  have shape : shapeOfHOLExact value=kind.resultShape := (shapeEqHOL_eq_true _ _).mp checked
  refine ⟨target,value,⟨next,globals,fields.2.2.2,fields.1,fields.2.1,fields.2.2.1,?_,?_⟩,shape,postEq⟩
  · rwa [postClock] at clock
  · rwa [postClock] at price

end InitECandidate.Solver.Headers.Helper

#print axioms InitECandidate.Solver.Headers.Helper.assigned_normal
