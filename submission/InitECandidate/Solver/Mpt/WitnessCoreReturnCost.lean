import InitECandidate.Solver.Mpt.WitnessCoreReturnProgram
import InitECandidate.Solver.Mpt.NodeConstructorCost
import InitECandidate.Solver.Mpt.FailGuard
import InitECandidate.Solver.Rlp.ItemCallFrame

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem parent_metadata_quiet (code) (name : String) : Input.QuietClock.Preserves code (parentMetadata name) := by
  unfold parentMetadata popWith writeAt
  repeat' first
    | apply Input.QuietClock.sequence
    | exact Input.QuietClock.store code _ _
    | exact Input.QuietClock.assign code _ _

theorem cache_return_hash_quiet (code) : Input.QuietClock.Preserves code cacheReturnHash := by
  rw [cache_return_hash_shape]
  exact Input.QuietClock.conditional code _ _ _ (Input.QuietClock.store code _ _) (Input.QuietClock.skip code)

theorem branch_advance_quiet (code) : Input.QuietClock.Preserves code branchAdvance := by
  rw [branch_advance_shape]
  unfold writeAt
  repeat' first
    | apply Input.QuietClock.sequence
    | exact Input.QuietClock.store code _ _
    | exact Input.QuietClock.assign code _ _

theorem branch_value_writes_quiet (code) : Input.QuietClock.Preserves code branchValueWrites := by
  rw [branch_value_writes_shape]
  unfold writeAt
  repeat' first
    | apply Input.QuietClock.conditional
    | apply Input.QuietClock.sequence
    | exact Input.QuietClock.store code _ _
    | exact Input.QuietClock.assign code _ _
    | exact Input.QuietClock.skip code

private theorem fail_guard_price (code) (installed : Input.OriginalCode.Installed code)
    (test : ExpHOL 64) (error : BitVec 64) (rest : ProgHOL 64) (price : Nat) (tail : Input.ClockCost.Bound code rest price) :
    Input.ClockCost.Bound code (.seq (.ite test (returnFail error) .skip) rest) (max 1 price) := by
  intro source codeEq
  have actual : Input.OriginalCode.Installed source.code:=by rw [codeEq]; exact installed
  exact Fail.guard_reached_cost source test error rest price actual (fun _=>tail source codeEq)

/-- The complete original extension return path has at most three source
ticks on every outcome: either real failure guard or original node_new_ext
and its allocator, followed by quiet metadata/pop/local assignments. -/
theorem return_extension_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code returnExtension 3 := by
  have tail : Input.ClockCost.Bound code afterExtensionCreate 0:=by
    rw [after_extension_create_shape]
    exact Input.ClockCost.of_quiet code _ (parent_metadata_quiet code "ex")
  have create : Input.ClockCost.Bound code extensionCreate 3:=by
    rw [extension_create_shape]
    exact Input.ClockCost.scoped_body code (ofString "ex") .one (ofString "node_new_ext") extensionArguments afterExtensionCreate
      (NodeConstructor.formals .extension) (NodeConstructor.body .extension) .one 2 0
      (NodeConstructor.original_code .extension code installed) (NodeConstructor.scalar_body_price .extension (by decide) code installed) tail
  have afterKind : Input.ClockCost.Bound code afterExtensionKind 3:=by
    rw [after_extension_kind_shape]
    exact fail_guard_price code installed extensionKindTest 8#64 extensionCreate 3 create
  have readKind : Input.ClockCost.Bound code extensionKindRead 3:=by
    rw [extension_kind_read_shape]
    exact Input.ClockCost.declared code (ofString "ck") .one (readAt "result" 0#64) afterExtensionKind 3 afterKind
  rw [return_extension_shape]
  exact fail_guard_price code installed (.cmp .equal (localVar "result") (.const 0#64)) 8#64 extensionKindRead 3 readKind

theorem after_branch_value_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code afterBranchValue 1 := by
  have tail : Input.ClockCost.Bound code branchFinishTail 1:=by
    rw [branch_finish_tail_shape]
    have metadata : Input.ClockCost.Bound code branchMetadata 0:=by
      rw [branch_metadata_shape]
      exact Input.ClockCost.of_quiet code _ (parent_metadata_quiet code "br")
    have failPrice : Input.ClockCost.Bound code (returnFail 9#64) 1:=Fail.call_price code installed [.const 9#64]
    exact Input.ClockCost.sequence code _ _ 1 0
      (Input.ClockCost.conditional code _ _ _ 1 0 failPrice (Input.ClockCost.skip code)) metadata
  have body : Input.ClockCost.Bound code branchValueBody 1:=by
    rw [branch_value_body_shape]
    exact Input.ClockCost.sequence code _ _ 0 1 (Input.ClockCost.of_quiet code _ (branch_value_writes_quiet code)) tail
  rw [after_branch_value_shape]
  exact Input.ClockCost.declared code (ofString "occ") .one (readAt "top" 40#64) branchValueBody 1 body

/-- The actual final-child row16 item caller and its whole occupancy/
value/metadata/pop continuation. Present physical row reads supply args;
the item result and all later outcomes are unrestricted. -/
theorem branch_value_call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) branchValueArguments=some (Rlp.Header.values pointer length))
    (arena : Rlp.Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source branchValueCall).2.clock≤60*length.toNat+43 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩:=Rlp.environment source.code.lookup (ofString "rlp_item") Rlp.Item.body Rlp.Item.resultShape pointer length (Rlp.Item.original_code source.code installed)
  let entry:=callEntryStateHOLFinite source callee
  have entryArena:=arena.of_fields source entry cursor limit rfl rfl
  have bodyCost:=Rlp.Item.body_cost entry pointer length cursor limit pointerLocal lengthLocal entryArena fits installed
  have priced:=Input.ClockCost.scoped_current source (ofString "bv") Rlp.Item.resultShape (ofString "rlp_item") branchValueArguments _ Rlp.Item.body afterBranchValue callee Rlp.Item.resultShape
    (60*length.toNat+41) 1 args called bodyCost (after_branch_value_price source.code installed)
  rw [branch_value_call_shape]
  exact priced.trans (by omega)

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.parent_metadata_quiet
#print axioms InitECandidate.Solver.Mpt.WitnessCore.cache_return_hash_quiet
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_advance_quiet
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_value_writes_quiet
#print axioms InitECandidate.Solver.Mpt.WitnessCore.return_extension_price
#print axioms InitECandidate.Solver.Mpt.WitnessCore.after_branch_value_price
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_value_call_cost
