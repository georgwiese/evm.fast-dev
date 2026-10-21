import InitECandidate.Solver.Mpt.WitnessResolveProgram
import InitECandidate.Solver.Mpt.NodeConstructorCost
import InitECandidate.Solver.MutableTable.WitnessDatabaseAnyCost
import InitECandidate.Solver.MutableTable.WitnessDatabaseFields
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

theorem lookup_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array table scratch pointer header payload flag : BitVec 64)
    (count maximum : Nat) (slices : Nat→Graph.Slice)
    (actual : MutableTable.WitnessBuild.Database source array table count maximum slices scratch)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word table)))
    (itemCell : source.locals.lookup (ofString "it")=some (Rlp.Item.result pointer header payload flag))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source lookupCall).2.clock≤6*count+7 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) queryArguments=
      some (MutableTable.NodeDb.arguments table (pointer+header)) := by
    simp [queryArguments,field,QueryBranch.localVar,Rlp.Item.result,MutableTable.NodeDb.arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,dbCell,itemCell]
  obtain ⟨callee,called,dbLocal,hashLocal⟩:=MutableTable.NodeDb.environment source.code.lookup table (pointer+header) (MutableTable.NodeDb.original_code source.code installed)
  let entry:=callEntryStateHOLFinite source callee
  have actualEntry:=actual.of_fields source entry array table count maximum slices scratch rfl rfl rfl
  have priced:=actualEntry.any_body_cost entry array table count maximum slices scratch (pointer+header) installed dbLocal hashLocal
  exact Input.ClockCost.scoped_current source (ofString "r") MutableTable.NodeDb.resultShape (ofString "nodedb_lookup") queryArguments _ MutableTable.NodeDb.body afterLookup callee MutableTable.NodeDb.resultShape
    (6*count+3) 3 args called priced (lookup_tail_price source.code installed)

/-- Every actual resolver suffix is bounded from the present physical
database and actual parsed item. Query readability, lookup success and
normal node allocation are not premises. -/
theorem suffix_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array table scratch pointer header payload flag : BitVec 64)
    (count maximum : Nat) (slices : Nat→Graph.Slice)
    (actual : MutableTable.WitnessBuild.Database source array table count maximum slices scratch)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word table)))
    (itemCell : source.locals.lookup (ofString "it")=some (Rlp.Item.result pointer header payload flag))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (WitnessStep.afterRlp .resolve)).2.clock≤6*count+7 := by
  have lookupPrice:=lookup_cost source array table scratch pointer header payload flag count maximum slices actual dbCell itemCell installed
  have sizePrice:=Input.ClockCost.stopping_guard_reached source sizeTest wrongSize lookupCall 1 (6*count+7)
    (fun passed=>Fail.call_not_normal source _ installed [.const 10#64] (Prod.ext passed rfl)) (Fail.call_price source.code installed [.const 10#64] source rfl) (fun _=>lookupPrice)
  have afterPrice : source.clock-(evaluateHOLFiniteState source afterEmpty).2.clock≤6*count+7:=sizePrice.trans (by omega)
  have emptyStops : (evaluateHOLFiniteState source emptyReturn).1≠none:=Input.NoFallthrough.returned _ source
  have emptyPrice : source.clock-(evaluateHOLFiniteState source emptyReturn).2.clock≤0:=
    Input.ClockCost.of_quiet source.code _ (Input.QuietClock.returned source.code _) source rfl
  have stringPrice:=Input.ClockCost.stopping_guard_reached source emptyTest emptyReturn afterEmpty 0 (6*count+7) emptyStops emptyPrice (fun _=>afterPrice)
  have conditionalPrice:=Input.ClockCost.conditional_current source stringTest stringBranch .skip (6*count+7) 0
    (stringPrice.trans (by omega)) (by simp only [evaluateHOLFiniteState_skip,Nat.sub_self,Nat.le_refl])
  rw [suffix_shape]
  exact Input.ClockCost.sequence_current source _ listReturn (6*count+7) 0 (conditionalPrice.trans (by omega))
    (Input.ClockCost.of_quiet source.code _ (Input.QuietClock.returned source.code _))

end InitECandidate.Solver.Mpt.WitnessResolve

#print axioms InitECandidate.Solver.Mpt.WitnessResolve.lookup_tail_price
#print axioms InitECandidate.Solver.Mpt.WitnessResolve.lookup_cost
#print axioms InitECandidate.Solver.Mpt.WitnessResolve.suffix_cost
