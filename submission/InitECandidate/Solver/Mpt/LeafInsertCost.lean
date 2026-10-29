import InitECandidate.Solver.Mpt.LeafInsertDispatch
import InitECandidate.Solver.Mpt.CommonPrefixCall
import InitECandidate.Solver.MutableTable.MemeqVariableCost
import InitECandidate.Solver.MutableTable.MemeqAnyCall
import InitECandidate.Solver.Input.ClockCostDeclaredReached

namespace InitECandidate.Solver.Mpt.InsertLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem split_scope_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (left el right rl : BitVec 64)
    (small : rl.toNat≤64) (installed : Input.OriginalCode.Installed source.code)
    (leftCell : source.locals.lookup (ofString "ek")=some (.val (.word left)))
    (elCell : source.locals.lookup (ofString "el")=some (.val (.word el)))
    (rightCell : source.locals.lookup (ofString "rk")=some (.val (.word right)))
    (rlCell : source.locals.lookup (ofString "rl")=some (.val (.word rl))) :
    source.clock-(evaluateHOLFiniteState source splitScope).2.clock≤rl.toNat+241 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) prefixArguments=
      some (CommonPrefix.values left el right rl):=by
    simp [prefixArguments,CommonPrefix.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,leftCell,elCell,rightCell,rlCell]
  obtain ⟨callee,called,_,al,_,bl⟩:=CommonPrefix.environment source.code.lookup left el right rl (CommonPrefix.original_code source.code installed)
  have bodyPrice:=CommonPrefix.body_cost (callEntryStateHOLFinite source callee) el rl
    (Nat.le_trans (Nat.min_le_right _ _) small) installed al bl
  rw [dispatch_shapes.2.2.2.2.2]
  have priced:=Input.ClockCost.scoped_current source (ofString "pl") .one (ofString "common_prefix_length") prefixArguments _ CommonPrefix.body afterPrefix
    callee .one (min el.toNat rl.toNat+1) 239 args called bodyPrice (after_prefix_price source.code installed)
  exact Nat.le_trans priced (by have bound:=Nat.min_le_right el.toNat rl.toNat; omega)

theorem length_choice_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (left el right rl : BitVec 64)
    (small : rl.toNat≤64) (installed : Input.OriginalCode.Installed source.code)
    (leftCell : source.locals.lookup (ofString "ek")=some (.val (.word left)))
    (elCell : source.locals.lookup (ofString "el")=some (.val (.word el)))
    (rightCell : source.locals.lookup (ofString "rk")=some (.val (.word right)))
    (rlCell : source.locals.lookup (ofString "rl")=some (.val (.word rl))) :
    source.clock-(evaluateHOLFiniteState source lengthChoice).2.clock≤4*rl.toNat+1 := by
  rw [dispatch_shapes.2.2.2.1]
  by_cases same : el=rl
  · have observed : eval source lengthTest=some (.val (.word 1#64)):=by
      simp [eval,lengthTest,evalHOLExact,toExact,localVar,elCell,rlCell,same,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    simp only [eval] at observed
    rw [evaluateHOLFiniteState_ite,observed]
    change source.clock-(evaluateHOLFiniteState source compareScope).2.clock≤_
    have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) compareArguments=
        some (MutableTable.MemeqByteRuntime.values left right rl.toNat):=by
      simp [compareArguments,MutableTable.MemeqByteRuntime.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,leftCell,elCell,rightCell,same]
    obtain ⟨callee,called,a,b,n⟩:=MutableTable.MemeqByteRuntime.environment source.code.lookup left right rl.toNat
      (MutableTable.MemeqAny.original_code source.code installed)
    have priced:=MutableTable.MemeqAny.variable_body_cost (callEntryStateHOLFinite source callee) rl.toNat small n
    rw [dispatch_shapes.2.2.2.2.1]
    exact Input.ClockCost.scoped_current source (ofString "eq") .one (ofString "memeq") compareArguments _ Memeq32.body compareGuard callee .one
      (4*rl.toNat) 0 args called priced (Input.ClockCost.of_quiet source.code compareGuard (compare_guard_quiet source.code))
  · have observed : eval source lengthTest=some (.val (.word 0#64)):=by
      simp [eval,lengthTest,evalHOLExact,toExact,localVar,elCell,rlCell,same,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    simp only [eval] at observed
    rw [evaluateHOLFiniteState_ite,observed]
    simp [evaluateHOLFiniteState_skip]

theorem after_length_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (left el right rl : BitVec 64)
    (small : rl.toNat≤64) (installed : Input.OriginalCode.Installed source.code)
    (leftCell : source.locals.lookup (ofString "ek")=some (.val (.word left)))
    (elCell : source.locals.lookup (ofString "el")=some (.val (.word el)))
    (rightCell : source.locals.lookup (ofString "rk")=some (.val (.word right)))
    (rlCell : source.locals.lookup (ofString "rl")=some (.val (.word rl))) :
    source.clock-(evaluateHOLFiniteState source afterLength).2.clock≤5*rl.toNat+242 := by
  rw [dispatch_shapes.2.2.1]
  have price:=Input.ClockCost.sequence_reached_current source lengthChoice splitScope (4*rl.toNat+1) (rl.toNat+241)
    (length_choice_cost source left el right rl small installed leftCell elCell rightCell rlCell) (by
      intro middle normal
      have saved (key : MlS) (different : key≠ofString "eq") : middle.locals.lookup key=source.locals.lookup key:=by
        have info:=(length_choice_flow key different).summary source
        unfold Input.FlowSummary at info
        rw [normal] at info
        exact info.1 rfl
      have codeEq:=(Input.evaluation_fields source middle lengthChoice none normal).2.2.2
      exact split_scope_cost middle left el right rl small (by rw [codeEq]; exact installed)
        ((saved _ (by decide)).trans leftCell) ((saved _ (by decide)).trans elCell)
        ((saved _ (by decide)).trans rightCell) ((saved _ (by decide)).trans rlCell))
  omega

theorem after_key_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (left right rl : BitVec 64)
    (small : rl.toNat≤64) (installed : Input.OriginalCode.Installed source.code)
    (leftCell : source.locals.lookup (ofString "ek")=some (.val (.word left)))
    (rightCell : source.locals.lookup (ofString "rk")=some (.val (.word right)))
    (rlCell : source.locals.lookup (ofString "rl")=some (.val (.word rl))) :
    source.clock-(evaluateHOLFiniteState source afterKey).2.clock≤5*rl.toNat+242 := by
  rw [dispatch_shapes.2.1]
  apply Input.ClockCost.declared_reached_current
  intro loaded read checked
  cases loaded with
  | val payload=>
    cases payload with
    | word el=>
      let current:=bind source "el" el
      exact after_length_cost current left el right rl small installed
        ((bind_lookup_other source "el" "ek" el (by decide)).trans leftCell) (bind_lookup_same _ _ _)
        ((bind_lookup_other source "el" "rk" el (by decide)).trans rightCell)
        ((bind_lookup_other source "el" "rl" el (by decide)).trans rlCell)
  | rStruct fields=>simp [shapeEqHOL,shapeOfHOLExact] at checked
  | nStruct name fields=>simp [shapeEqHOL,shapeOfHOLExact] at checked

/-- Every outcome of the unchanged original249 leaf insertion, including
unmapped header/path reads, short clocks, replacement, splitting and
allocation/collision failures. Only the real scalar key and its current
length<=64 are needed; successful graph mutation is not assumed. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (right rl : BitVec 64)
    (small : rl.toNat≤64) (installed : Input.OriginalCode.Installed source.code)
    (rightCell : source.locals.lookup (ofString "rk")=some (.val (.word right)))
    (rlCell : source.locals.lookup (ofString "rl")=some (.val (.word rl))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤5*rl.toNat+242 := by
  rw [dispatch_shapes.1]
  apply Input.ClockCost.declared_reached_current
  intro loaded read checked
  cases loaded with
  | val payload=>
    cases payload with
    | word left=>
      let current:=bind source "ek" left
      exact after_key_cost current left right rl small installed (bind_lookup_same _ _ _)
        ((bind_lookup_other source "ek" "rk" left (by decide)).trans rightCell)
        ((bind_lookup_other source "ek" "rl" left (by decide)).trans rlCell)
  | rStruct fields=>simp [shapeEqHOL,shapeOfHOLExact] at checked
  | nStruct name fields=>simp [shapeEqHOL,shapeOfHOLExact] at checked

end InitECandidate.Solver.Mpt.InsertLeaf

#print axioms InitECandidate.Solver.Mpt.InsertLeaf.split_scope_cost
#print axioms InitECandidate.Solver.Mpt.InsertLeaf.length_choice_cost
#print axioms InitECandidate.Solver.Mpt.InsertLeaf.after_length_cost
#print axioms InitECandidate.Solver.Mpt.InsertLeaf.after_key_cost
#print axioms InitECandidate.Solver.Mpt.InsertLeaf.body_cost
