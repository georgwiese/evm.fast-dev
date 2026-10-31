import InitECandidate.Solver.Mpt.WitnessResolveProgram
import InitECandidate.Solver.Mpt.NodeConstructorCost
import InitECandidate.Solver.Input.CurrentTable.NodeLookup.Call
import InitECandidate.Solver.Input.WordPairEnvironment
import InitECandidate.Solver.Mpt.Fail
import InitECandidate.Solver.Input.NoFallthrough
import InitECandidate.Solver.Input.ClockCostGuardReached
import InitECandidate.Solver.Input.ClockCostCurrentConditional

namespace InitECandidate.Solver.Mpt.WitnessResolve
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

theorem lookup_tail_price (code) (installed : Input.OriginalCode.Installed code) :
    Input.ClockCost.Bound code afterLookup 3 := by
  have quietReturn (expression : ExpHOL 64) := Input.ClockCost.of_quiet code (.return expression) (Input.QuietClock.returned code expression)
  have hashPrice : Input.ClockCost.Bound code hashCall 3 :=
    Input.ClockCost.scoped_body code (ofString "hn") .one (ofString "node_new_hashed") [field "it" 1] hashReturn
      (NodeConstructor.formals .hashed) (NodeConstructor.body .hashed) .one 2 0
      (NodeConstructor.original_code .hashed code installed) (NodeConstructor.scalar_body_price .hashed (by decide) code installed) (quietReturn _)
  exact Input.ClockCost.sequence code _ _ 3 0
    (Input.ClockCost.conditional code _ _ _ 3 0 hashPrice (Input.ClockCost.of_quiet code _ (Input.QuietClock.skip code))) (quietReturn _)

theorem lookup_cost (data : Input.CurrentTable.NodeBuild.Data) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer header payload flag : BitVec 64)
    (actual : Input.CurrentTable.NodeLookup.Database source data)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word data.table)))
    (itemCell : source.locals.lookup (ofString "it")=some (Rlp.Item.result pointer header payload flag))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source lookupCall).2.clock≤268 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) queryArguments=
      some [.val (.word data.table),.val (.word (pointer+header))] := by
    simp [queryArguments,field,QueryBranch.localVar,Rlp.Item.result,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,dbCell,itemCell]
  obtain ⟨callee,called,dbLocal,hashLocal⟩:=Input.word_pair_environment source.code.lookup (ofString "nodedb_lookup") (ofString "db") (ofString "hash")
    Input.CurrentTable.NodeLookup.body Input.CurrentTable.NodeLookup.resultShape data.table (pointer+header) (by decide)
    (Input.CurrentTable.NodeLookup.original_code source.code installed)
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨root,next,count,valid,bits,left,right,keys,image,bounded⟩:=actual.image
  have priced:=Input.CurrentTable.NodeLookup.body_cost entry data.table data.cap root (pointer+header) next count valid bits left right keys
    (Input.CurrentTable.NodeBuild.ValueOf data) (image.of_frame rfl) dbLocal hashLocal installed
  exact Input.ClockCost.scoped_current source (ofString "r") Input.CurrentTable.NodeLookup.resultShape (ofString "nodedb_lookup") queryArguments _
    Input.CurrentTable.NodeLookup.body afterLookup callee Input.CurrentTable.NodeLookup.resultShape 264 3 args called priced (lookup_tail_price source.code installed)

/-- Every actual resolver suffix is bounded from the present physical
database and actual parsed item. Query readability, lookup success and
normal node allocation are not premises. -/
theorem suffix_cost (data : Input.CurrentTable.NodeBuild.Data) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer header payload flag : BitVec 64)
    (actual : Input.CurrentTable.NodeLookup.Database source data)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word data.table)))
    (itemCell : source.locals.lookup (ofString "it")=some (Rlp.Item.result pointer header payload flag))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (WitnessStep.afterRlp .resolve)).2.clock≤268 := by
  have lookupPrice:=lookup_cost data source pointer header payload flag actual dbCell itemCell installed
  have sizePrice:=Input.ClockCost.stopping_guard_reached source sizeTest wrongSize lookupCall 1 (268)
    (fun passed=>Fail.call_not_normal source _ installed [.const 10#64] (Prod.ext passed rfl)) (Fail.call_price source.code installed [.const 10#64] source rfl) (fun _=>lookupPrice)
  have afterPrice : source.clock-(evaluateHOLFiniteState source afterEmpty).2.clock≤268:=sizePrice.trans (by omega)
  have emptyStops : (evaluateHOLFiniteState source emptyReturn).1≠none:=Input.NoFallthrough.returned _ source
  have emptyPrice : source.clock-(evaluateHOLFiniteState source emptyReturn).2.clock≤0:=
    Input.ClockCost.of_quiet source.code _ (Input.QuietClock.returned source.code _) source rfl
  have stringPrice:=Input.ClockCost.stopping_guard_reached source emptyTest emptyReturn afterEmpty 0 (268) emptyStops emptyPrice (fun _=>afterPrice)
  have conditionalPrice:=Input.ClockCost.conditional_current source stringTest stringBranch .skip (268) 0
    (stringPrice.trans (by omega)) (by simp only [evaluateHOLFiniteState_skip,Nat.sub_self,Nat.le_refl])
  rw [suffix_shape]
  exact Input.ClockCost.sequence_current source _ listReturn (268) 0 (conditionalPrice.trans (by omega))
    (Input.ClockCost.of_quiet source.code _ (Input.QuietClock.returned source.code _))

end InitECandidate.Solver.Mpt.WitnessResolve

#print axioms InitECandidate.Solver.Mpt.WitnessResolve.lookup_tail_price
#print axioms InitECandidate.Solver.Mpt.WitnessResolve.lookup_cost
#print axioms InitECandidate.Solver.Mpt.WitnessResolve.suffix_cost
