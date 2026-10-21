import InitECandidate.Solver.Headers.HelperBody
import InitECandidate.Solver.Input.ScopedCallTrace

namespace InitECandidate.Solver.Headers.Helper
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Current slice evidence depends on physical data and arena globals,
so installing an actual callee's locals preserves it. -/
theorem entry_state (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (array pointer cursor limit : BitVec 64)
    (bytes cutoff : Nat) (items : List Rlp.ListItem) (state : SliceState source pointer array cursor limit bytes cutoff items) :
    SliceState (callEntryStateHOLFinite source callee) pointer array cursor limit bytes cutoff items :=
  state.of_parts source _ pointer array cursor limit bytes cutoff items
    (Rlp.Validation.Arena.of_fields source _ cursor limit state.arena rfl rfl) state.records (by intro offset inside; rfl)

/-- Every actual assigned/ignored original header helper caller is charged
from its real selected row, with the original callee ABI and one caller tick. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (array pointer cursor limit control : BitVec 64) (bytes cutoff index : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (state : SliceState source pointer array cursor limit bytes cutoff items) (selected : items[index]?=some item)
    (destination : Option (Option MlS)) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some (kind.values array (BitVec.ofNat 64 index) control))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (.call (Input.LocalEffects.callInfo destination) kind.name expressions)).2.clock≤kind.bodyPrice item.total.toNat+1 := by
  obtain ⟨callee,called,arrayCell,indexCell,controlCell⟩ := environment source.code.lookup kind array (BitVec.ofNat 64 index) control (original_code source.code installed kind)
  have ready:=entry_state source callee array pointer cursor limit bytes cutoff items state
  have price:=body_cost (callEntryStateHOLFinite source callee) kind array pointer cursor limit control bytes cutoff index items item ready selected arrayCell indexCell controlCell installed
  exact Input.ClockCost.call_current source destination kind.name expressions _ kind.body callee kind.resultShape (kind.bodyPrice item.total.toNat) args called price

/-- Real original helper return data available before its continuation:
actual state, unchanged globals/immutable metadata and paid caller clocks. -/
structure Returned (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (array pointer cursor limit : BitVec 64) (bytes cutoff rowBytes : Nat) (items : List Rlp.ListItem) : Prop where
  state : SliceState target pointer array cursor limit bytes cutoff items
  globals : ∀ key,target.globals.lookup key=source.globals.lookup key
  code : target.code=source.code
  domain : target.memaddrs=source.memaddrs
  endian : target.be=source.be
  exceptions : target.eshapes=source.eshapes
  forward : target.clock≤source.clock
  cost : source.clock-target.clock≤kind.bodyPrice rowBytes+1

/-- All enclosing outcomes of the actual scoped original helper: stop
within its own allowance or enter the true continuation with a checked
return and derived next physical slice state. -/
theorem scoped_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (array pointer cursor limit control : BitVec 64) (bytes cutoff index : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (state : SliceState source pointer array cursor limit bytes cutoff items) (selected : items[index]?=some item)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some (kind.values array (BitVec.ofNat 64 index) control))
    (installed : Input.OriginalCode.Installed source.code) (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) kind.resultShape kind.name expressions continuation)=(result,post)) :
    source.clock-post.clock≤kind.bodyPrice item.total.toNat+1 ∨
      ∃ target value inner,Returned source target kind array pointer cursor limit bytes cutoff item.total.toNat items ∧
        shapeOfHOLExact value=kind.resultShape ∧
        evaluateHOLFiniteState (Input.CallNormal.continuationEntry source target name value) continuation=(result,inner) ∧
        post=WitnessRadix.QueryBranch.restore source name inner := by
  obtain ⟨callee,called,arrayCell,indexCell,controlCell⟩ := environment source.code.lookup kind array (BitVec.ofNat 64 index) control (original_code source.code installed kind)
  let entry:=callEntryStateHOLFinite source callee
  have ready:=entry_state source callee array pointer cursor limit bytes cutoff items state
  have price:=body_cost entry kind array pointer cursor limit control bytes cutoff index items item ready selected arrayCell indexCell controlCell installed
  rcases Input.CallNormal.scoped_trace source post name kind.resultShape kind.name expressions _ kind.body continuation callee kind.resultShape
      (kind.bodyPrice item.total.toNat) args called price result run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨target,value,inner,funded,bodyRun,checked,forward,cost,continued,endpoint⟩ := reached
    obtain ⟨next,globals⟩ := body_normal_state entry target kind array pointer cursor limit control bytes cutoff index items item ready selected arrayCell indexCell controlCell installed value bodyRun
    have fields:=Input.evaluation_fields entry target kind.body (some (.returned value)) bodyRun
    have shape : shapeOfHOLExact value=kind.resultShape := (shapeEqHOL_eq_true _ _).mp (Bool.and_eq_true_iff.mp checked).1
    exact Or.inr ⟨target,value,inner,⟨next,globals,fields.2.2.2,fields.1,fields.2.1,fields.2.2.1,forward,cost⟩,shape,continued,endpoint⟩

end InitECandidate.Solver.Headers.Helper

#print axioms InitECandidate.Solver.Headers.Helper.entry_state
#print axioms InitECandidate.Solver.Headers.Helper.call_cost
#print axioms InitECandidate.Solver.Headers.Helper.scoped_trace
