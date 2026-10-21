import InitECandidate.Solver.Mpt.NodeConstructorFields
import InitECandidate.Solver.WitnessRadix.AllocationTrace
import InitECandidate.Solver.WitnessRadix.ZeroCost
import InitECandidate.Solver.Input.ClockCostCurrent

namespace InitECandidate.Solver.Mpt.NodeConstructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def branchArguments : List (ExpHOL 64):=[QueryBranch.localVar "nd",.const 176#64]
def branchZero : ProgHOL 64:=.call (some (none,none)) (ofString "memzero") branchArguments
def branchFields : List FieldStores.Field:=[⟨0,.literal 3#64⟩]
def branchFooter : ProgHOL 64:=FieldStores.program "nd" "" branchFields (.return (QueryBranch.localVar "nd"))

set_option maxRecDepth 100000 in
theorem branch_tail_shape : tail .branch=.seq branchZero branchFooter := by
  simp only [tail,body,original,branchZero,branchArguments,branchFooter,branchFields,FieldStores.program,FieldStores.address,
    FieldStores.Value.expression,QueryBranch.addConst,QueryBranch.localVar,Guest.guestFn_node_new_branch,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]

theorem branch_footer_quiet (code) : Input.QuietClock.Preserves code branchFooter := by
  exact Input.QuietClock.sequence code _ _ (Input.QuietClock.store code _ _) (Input.QuietClock.returned code _)

theorem branch_tail_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (node : source.locals.lookup (ofString "nd")=some (.val (.word heap)))
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena heap 176) (aligned : heap.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (tail .branch)).2.clock≤8 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) branchArguments=some (Zero.values heap 176) := by
    simp [branchArguments,Zero.values,QueryBranch.localVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,node]
  have price:=Zero.call_cost source branchArguments heap 176 args (Zero.original_code source.code installed) (by decide) (by decide) aligned
    (fun offset inside offsetAligned=>AllocatedBytes.word_mapped source heap 176 offset domain arena (by omega) aligned offsetAligned)
  rw [branch_tail_shape]
  exact Input.ClockCost.sequence_current source branchZero branchFooter 8 0 price (Input.ClockCost.of_quiet source.code _ (branch_footer_quiet source.code))

/-- All outcomes of the unchanged branch constructor, deriving its real
176-byte room only when allocation actually reaches the zeroing suffix. -/
theorem branch_body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (body .branch)).2.clock≤9 := by
  let output:=evaluateHOLFiniteState source (body .branch)
  have actual : evaluateHOLFiniteState source (.decCall (ofString "nd") .one (ofString "alloc") [.const 176#64] (tail .branch))=(output.1,output.2):=by
    have shape:=allocation_shape .branch
    change body .branch=.decCall (ofString "nd") .one (ofString "alloc") [.const 176#64] (tail .branch) at shape
    rw [←shape]
  rcases PersistentAlloc.scoped_trace source output.2 "nd" [.const 176#64] (tail .branch) heap 176#64 rfl installed heapCell (by have upper:=arena.upper; omega) output.1 actual with stopped|reached
  · exact stopped.trans (by omega)
  · obtain ⟨funded,room,inner,continued,endpoint⟩:=reached
    let ready:=QueryBranch.bind (PersistentAlloc.post {source with clock:=source.clock-1} heap 176#64) "nd" heap
    have node : ready.locals.lookup (ofString "nd")=some (.val (.word heap)):=QueryBranch.bind_lookup_same _ _ _
    have nodeArena : AllocatedBytes.Arena heap 176:=⟨arena.lower,room⟩
    have tailPrice:=branch_tail_cost ready heap node domain nodeArena aligned installed
    rw [continued] at tailPrice
    change source.clock-1-inner.clock≤8 at tailPrice
    have forward:=evaluateHOLFiniteState_clock_le ready (tail .branch)
    rw [continued] at forward
    change inner.clock≤source.clock-1 at forward
    have finalClock : output.2.clock=inner.clock:=by rw [endpoint]; rfl
    change source.clock-output.2.clock≤9
    rw [finalClock]
    omega

end InitECandidate.Solver.Mpt.NodeConstructor

#print axioms InitECandidate.Solver.Mpt.NodeConstructor.branch_tail_shape
#print axioms InitECandidate.Solver.Mpt.NodeConstructor.branch_footer_quiet
#print axioms InitECandidate.Solver.Mpt.NodeConstructor.branch_tail_cost
#print axioms InitECandidate.Solver.Mpt.NodeConstructor.branch_body_cost
