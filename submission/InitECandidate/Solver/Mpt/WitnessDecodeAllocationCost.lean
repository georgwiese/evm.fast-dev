import InitECandidate.Solver.Mpt.WitnessDecodeRecordNormal
import InitECandidate.Solver.Mpt.FailGuard
import InitECandidate.Solver.Mpt.NodeConstructorCost
import InitECandidate.Solver.Mpt.NodeBranchConstructor
import InitECandidate.Solver.Input.MainEntry
import InitECandidate.Solver.Input.ClockCostCurrentScoped
import InitECandidate.Solver.Input.ClockCostGuardReached

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

theorem record_call_price (kind : RecordKind) (code) (installed : Input.OriginalCode.Installed code) :
    Input.ClockCost.Bound code kind.call 2 := by
  rw [kind.call_shape]
  have quietTail : Input.QuietClock.Preserves code kind.tail:=by
    cases kind with
    | extension=>exact (tails_quiet code).1
    | branch=>exact (tails_quiet code).2.1
  exact Arenas.scoped_price code installed .down _ .one [.const 88#64] kind.tail 0 (Input.ClockCost.of_quiet code _ quietTail)

/-- Original extension zero-path rejection and its real record allocation,
including every failure, share the two-tick caller/trap allowance. -/
theorem extension_price (code) (installed : Input.OriginalCode.Installed code) :
    Input.ClockCost.Bound code extensionBody 2 := by
  intro source codeEq
  have currentInstalled : Input.OriginalCode.Installed source.code:=by rw [codeEq]; exact installed
  have price:=Fail.guard_reached_cost source (.cmp .equal (field "cn" 1) (.const 0#64)) 7#64 extensionAllocate 2 currentInstalled
    (fun _=>record_call_price .extension code installed source codeEq)
  have callShape:=RecordKind.call_shape .extension
  change extensionAllocate=.decCall (ofString "rec") .one (ofString "scratch_alloc") [.const 88#64] afterExtension at callShape
  rw [callShape] at price
  rw [extension_shape]
  exact price.trans (by decide)

theorem leaf_allocation_price (code) (installed : Input.OriginalCode.Installed code) :
    Input.ClockCost.Bound code leafAllocate 3 := by
  rw [leaf_shape]
  exact Input.ClockCost.scoped_body code (ofString "lf") .one (ofString "node_new_leaf") _ afterLeaf
    (NodeConstructor.formals .leaf) (NodeConstructor.body .leaf) .one 2 0
    (NodeConstructor.original_code .leaf code installed) (NodeConstructor.scalar_body_price .leaf (by decide) code installed)
    (Input.ClockCost.of_quiet code _ (tails_quiet code).2.2)

/-- The original branch decision, actual176-byte zeroed constructor and
88-byte record call, from the current real heap. Failed guards, reads and
allocations are included without successful allocation premises. -/
theorem branch_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source branchBody).2.clock≤12 := by
  obtain ⟨callee,called⟩:=Input.Main.nullary_environment source.code.lookup (ofString "node_new_branch") (NodeConstructor.body .branch)
    (NodeConstructor.original_code .branch source.code installed)
  have priced:=NodeConstructor.branch_body_cost (callEntryStateHOLFinite source callee) heap heapCell domain arena aligned installed
  have front:=Input.ClockCost.scoped_current source (ofString "br") .one (ofString "node_new_branch") [] []
    (NodeConstructor.body .branch) branchRecord callee .one 9 2 rfl called priced (record_call_price .branch source.code installed)
  have total:=Fail.guard_reached_cost source (.cmp .notEqual (field "sl" 1) (.const 17#64)) 4#64
    (.decCall (ofString "br") .one (ofString "node_new_branch") [] branchRecord) 12 installed (fun _=>front)
  have callShape:=RecordKind.call_shape .branch
  change branchRecord=.decCall (ofString "rec2") .one (ofString "scratch_alloc") [.const 88#64] afterBranchRecord at callShape
  rw [callShape] at total
  rw [branch_shape]
  exact total.trans (by decide)

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.record_call_price
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.extension_price
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.leaf_allocation_price
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.branch_cost
