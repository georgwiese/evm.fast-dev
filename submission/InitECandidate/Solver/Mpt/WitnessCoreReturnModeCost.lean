import InitECandidate.Solver.Mpt.WitnessCoreReturnDispatch
import InitECandidate.Solver.Mpt.WitnessCoreReturnCache
import InitECandidate.Solver.Mpt.WitnessCoreBranchCost

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Every outcome of the complete actual active return mode fits the
bounded final-value parser allowance. Entry ownership and ordered child
allocation protect the active record during the real pending-hash store;
the literal stage dispatch then pays extension<=3 or branch<=60*bytes+12.
This counts source call/loop ticks, not straight-line target instructions. -/
theorem return_mode_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db child hash cursor limit : BitVec 64) (data : WitnessRecord.Description)
    (view : WitnessRecord.View source record db data)
    (counts : ∀ node index occupied,data.payload=.branch node index occupied→ occupied.val≤index.val)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word record)))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word child)))
    (hashCell : source.memory (record+80#64)=.word hash)
    (ownership : child=0#64 ∨ AllocatedBytes.Arena child 32 ∧ child.toNat%8=0)
    (separated : hash≠0#64→ child≠0#64→ child.toNat+32≤2952790016 ∧ data.BeforeHeap child.toNat)
    (live : Rlp.LiveArena source) (arena : Rlp.Validation.Arena source cursor limit) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source returnBranch).2.clock≤60*data.bytes+12 := by
  let current:=QueryBranch.bind source "hash" hash
  let cached:=returnCacheState current child hash
  have currentView:=view.of_fields source current record db data rfl rfl
  have cachedView:=return_cache_view current record db child hash data currentView ownership separated
  have currentResult : current.locals.lookup (ofString "result")=some (.val (.word child)):=
    (bind_lookup_other source "hash" "result" hash (by decide)).trans resultCell
  have currentTop : current.locals.lookup (ofString "top")=some (.val (.word record)):=
    (bind_lookup_other source "hash" "top" hash (by decide)).trans topCell
  have cachedTop : cached.locals.lookup (ofString "top")=some (.val (.word record)):=by
    unfold cached returnCacheState
    split <;> exact currentTop
  have cachedResult : cached.locals.lookup (ofString "result")=some (.val (.word child)):=by
    unfold cached returnCacheState
    split <;> exact currentResult
  have cachedClock : cached.clock=source.clock:=by unfold cached returnCacheState; split <;> rfl
  have cachedGlobals : cached.globals=source.globals:=by unfold cached returnCacheState; split <;> rfl
  have cachedDomain : cached.memaddrs=source.memaddrs:=by unfold cached returnCacheState; split <;> rfl
  have cachedCode : cached.code=source.code:=by unfold cached returnCacheState; split <;> rfl
  have cachedArena:=arena.of_fields source cached cursor limit cachedDomain cachedGlobals
  have cachedLive : Rlp.LiveArena cached:=live.of_cursors cachedDomain cachedCode (by rw [cachedGlobals]) (by rw [cachedGlobals])
  have cachedInstalled : Input.OriginalCode.Installed cached.code:=by rw [cachedCode]; exact installed
  have priced : current.clock-(evaluateHOLFiniteState current afterReturnHash).2.clock≤60*data.bytes+12:=by
    rw [after_return_hash_trace current child hash view.rows.domain ownership (bind_lookup_same _ _ _) currentResult]
    change source.clock-(evaluateHOLFiniteState cached returnStages).2.clock≤60*data.bytes+12
    rw [←cachedClock,return_stages_choice cached record db data cachedView cachedTop]
    cases payloadEq : data.payload with
    | extension nibbles length=>
      have small:=return_extension_price cached.code cachedInstalled cached rfl
      exact small.trans (by omega)
    | branch node index occupied=>
      exact return_branch_node_cost cached record db node child cursor limit data index occupied (counts node index occupied payloadEq)
        cachedView payloadEq cachedTop cachedResult cachedLive cachedArena cachedInstalled
  have mapped : source.memaddrs (record+80#64):=by simpa only [byteAddress] using view.mapped source record db data 80 (by decide) (by decide)
  have read : eval source (readAt "top" 80#64)=some (.val (.word hash)):=by
    simp [eval,readAt,evalHOLExact,evalListHOLExact,localVar,toExact,topCell,valueIsWord,valueWord,wordOpHOL,wordOp,
      memLoadHOLExact,isWfShapeExactHOL,mapped,hashCell]
  have active:=Input.ClockCost.declared_current source "hash" (readAt "top" 80#64) hash afterReturnHash (60*data.bytes+12) read priced
  rw [return_choice source record topCell,if_neg (view.nonzero source record db data),active_return_shape]
  exact active

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.return_mode_cost
