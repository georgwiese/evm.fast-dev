import InitECandidate.Solver.Mpt.CurrentWitnessDecodeLeaf
import InitECandidate.Solver.Mpt.FailGuardReturn
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.Input.ScopedCallNormal
import InitECandidate.Solver.Input.NullaryEnvironment

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

set_option maxRecDepth 100000 in
theorem branch_allocate_shape : branchAllocate=
    .decCall (ofString "br") .one (ofString "node_new_branch") [] branchRecord := by
  simp only [branchAllocate,branchRecord,branchBody,afterArray,afterSlices,slicesCall,WitnessStep.afterRlp,WitnessStep.body,WitnessStep.original,
    seqRest,seqFirst,decRest,callRest,yesBranch,Guest.Software.guestFn__decode_step,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

theorem extension_body_shape : extensionBody=
    .seq (.ite (.cmp .equal (field "cn" 1) (.const 0#64)) (fail 7#64) .skip) extensionAllocate := by
  have tail : extensionAllocate=.decCall (ofString "rec") .one (ofString "scratch_alloc") [.const 88#64] afterExtension := by
    unfold extensionAllocate
    rw [extension_shape]
    rfl
  rw [extension_shape,←tail]

theorem branch_body_shape : branchBody=
    .seq (.ite (.cmp .notEqual (field "sl" 1) (.const 17#64)) (fail 4#64) .skip) branchAllocate := by
  have tail : branchAllocate=.decCall (ofString "br") .one (ofString "node_new_branch") []
      (.decCall (ofString "rec2") .one (ofString "scratch_alloc") [.const 88#64] afterBranchRecord) := by
    unfold branchAllocate
    rw [branch_shape]
    rfl
  rw [branch_shape,←tail]

theorem extension_body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (arena : Rlp.LiveArena source) :
    source.clock-(evaluateHOLFiniteState source extensionBody).2.clock≤2 := by
  exact suspended_extension_price source.code arena.code source rfl

set_option maxRecDepth 100000 in
theorem branch_record_call_shape : branchRecord=
    .decCall (ofString "rec2") .one (ofString "scratch_alloc") [.const 88#64] afterBranchRecord := by
  simp only [branchRecord,afterBranchRecord,branchAllocate,branchBody,afterArray,afterSlices,slicesCall,
    WitnessStep.afterRlp,WitnessStep.body,WitnessStep.original,callRest,seqRest,seqFirst,decRest,yesBranch,
    Guest.Software.guestFn__decode_step,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

set_option maxRecDepth 100000 in
/-- The actual branch scratch record includes all seven stores and its
successful suspended return, as well as allocation/store failures. -/
theorem branch_record_price (code) (installed : OriginalCode.Installed code) :
    ClockCost.Bound code branchRecord 2 := by
  rw [branch_record_call_shape]
  apply Arenas.scoped_price code installed .down (ofString "rec2") .one _ _ 0
  simp only [afterBranchRecord,branchRecord,branchAllocate,branchBody,afterArray,afterSlices,slicesCall,
    WitnessStep.afterRlp,WitnessStep.body,WitnessStep.original,callRest,seqRest,seqFirst,decRest,yesBranch,
    Guest.Software.guestFn__decode_step,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  repeat first
    | apply ClockCost.sequence (firstPrice:=0) (secondPrice:=0)
    | exact ClockCost.store code _ _
    | exact ClockCost.returned code _

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.branch_allocate_shape
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.extension_body_cost
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.branch_record_call_shape
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.branch_record_price
