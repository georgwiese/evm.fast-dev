import InitECandidate.Solver.Mpt.WitnessDecodeProgram
import InitECandidate.Solver.Input.ScratchStore
import InitECandidate.Solver.Input.CurrentStartup.ArenaState

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

set_option maxRecDepth 100000 in
theorem extension_allocate_shape : extensionAllocate=
    .decCall (ofString "rec") .one (ofString "scratch_alloc") [.const 88#64]
      (.seq (.store (Scalar.plus (localVar "rec") 8) (.const 1#64)) (seqRest afterExtension)) := by
  simp only [extensionBody,extensionAllocate,afterExtension,afterCompact,compactCall,afterPath,pairBody,afterArray,afterSlices,slicesCall,WitnessStep.afterRlp,WitnessStep.body,WitnessStep.original,seqRest,seqFirst,decRest,callRest,yesBranch,Scalar.plus,localVar,Guest.Software.guestFn__decode_step,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

set_option maxRecDepth 100000 in
theorem branch_record_shape : branchRecord=
    .decCall (ofString "rec2") .one (ofString "scratch_alloc") [.const 88#64]
      (.seq (.store (Scalar.plus (localVar "rec2") 8) (.const 2#64)) (seqRest afterBranchRecord)) := by
  simp only [branchRecord,afterBranchRecord,branchAllocate,branchBody,afterArray,afterSlices,slicesCall,WitnessStep.afterRlp,WitnessStep.body,WitnessStep.original,seqRest,decRest,callRest,yesBranch,Scalar.plus,localVar,Guest.Software.guestFn__decode_step,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

/-- The actual extension-frame allocation cannot pass its first store in
main's real scratch/domain configuration. Its later recursion is not assumed. -/
theorem extension_allocate_no_return (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (arena : CurrentStartup.ArenaState source) (value : ValueHOL 64) :
    evaluateHOLFiniteState source extensionAllocate≠(some (.returned value),post) := by
  rw [extension_allocate_shape]
  exact ScratchStore.allocated_no_return source post 2701127680#64 2688618496#64 88 8 "rec" 1#64 _ value
    (by decide) (by decide) (by decide) (by decide) (by decide) arena.domain arena.code arena.scratch arena.frame

theorem extension_allocate_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (arena : CurrentStartup.ArenaState source) :
    source.clock-(evaluateHOLFiniteState source extensionAllocate).2.clock≤2 := by
  rw [extension_allocate_shape]
  exact ScratchStore.allocated_price source 2701127680#64 2688618496#64 88 8 "rec" 1#64 _
    (by decide) (by decide) (by decide) (by decide) (by decide) arena.domain arena.code arena.scratch arena.frame

/-- The actual branch decoder reaches the same first-store boundary after
its branch-node constructor. This is a property of the real record suffix. -/
theorem branch_record_no_return (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (arena : CurrentStartup.ArenaState source) (value : ValueHOL 64) :
    evaluateHOLFiniteState source branchRecord≠(some (.returned value),post) := by
  rw [branch_record_shape]
  exact ScratchStore.allocated_no_return source post 2701127680#64 2688618496#64 88 8 "rec2" 2#64 _ value
    (by decide) (by decide) (by decide) (by decide) (by decide) arena.domain arena.code arena.scratch arena.frame

theorem branch_record_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (arena : CurrentStartup.ArenaState source) :
    source.clock-(evaluateHOLFiniteState source branchRecord).2.clock≤2 := by
  rw [branch_record_shape]
  exact ScratchStore.allocated_price source 2701127680#64 2688618496#64 88 8 "rec2" 2#64 _
    (by decide) (by decide) (by decide) (by decide) (by decide) arena.domain arena.code arena.scratch arena.frame

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.extension_allocate_shape
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.branch_record_shape
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.extension_allocate_no_return
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.extension_allocate_cost
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.branch_record_no_return
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.branch_record_cost
