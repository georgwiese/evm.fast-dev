import InitECandidate.Solver.Input.WitnessResolveBodyCost
import InitECandidate.Solver.Mpt.WitnessCoreResolveRows
import InitECandidate.Solver.Input.WordTripleEnvironment
import InitECandidate.Solver.Input.ClockCostCurrent

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang

theorem after_resolve_quiet (code) : Input.QuietClock.Preserves code afterResolve := by
  rw [after_resolve_shape,resolve_terminal_shape,resolve_decode_shape]
  repeat' first
    | apply Input.QuietClock.conditional
    | apply Input.QuietClock.sequence
    | exact Input.QuietClock.assign code _ _
    | exact Input.QuietClock.store code _ _

end InitECandidate.Solver.Mpt.WitnessCore

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Every outcome of the original core's resolve-mode block is priced
using the current record's selected row and the real main-built database.
The caller tick and both actual post-resolver continuations are included. -/
theorem core_resolve_cost (databaseData : CurrentTable.NodeBuild.Data) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record : BitVec 64) (data : Mpt.WitnessRecord.Description)
    (view : Mpt.WitnessRecord.View source record databaseData.table data) (database : CurrentTable.NodeLookup.Database source databaseData)
    (tableBefore : (CurrentTable.New.endPointer databaseData.table databaseData.cap).toNat≤2952790016)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word databaseData.table)))
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word record)))
    (slotCell : source.locals.lookup (ofString "slot")=some (.val (.word (BitVec.ofNat 64 data.payload.slotIndex))))
    (live : Rlp.LiveArena source) :
    source.clock-(evaluateHOLFiniteState source Mpt.WitnessCore.resolveBranch).2.clock≤
      60*data.bytes+282 := by
  have arrayRead:=Mpt.WitnessCore.resolve_array_read source record databaseData.table data view topCell
  obtain ⟨item,selected,args,positive,small,parentSmall,inputLower,beforeDb⟩:=Mpt.WitnessCore.resolve_row source record databaseData.table data view slotCell dbCell
  let ready:=QueryBranch.bind source "arr" data.array
  have readyDb : ready.locals.lookup (ofString "db")=some (.val (.word databaseData.table)):=
    (bind_lookup_other source "arr" "db" data.array (by decide)).trans dbCell
  have readyDatabase:=database.of_frame (show LocalEffects.erase ready=LocalEffects.erase source from rfl)
  obtain ⟨callee,called,dbLocal,pointerLocal,lengthLocal⟩:=word_triple_environment ready.code.lookup (ofString "_resolve_step")
    (ofString "db") (ofString "p") (ofString "n") (Mpt.WitnessStep.body .resolve) (.comb [.one,.one,.one,.one])
    databaseData.table (Rlp.Slices.itemPointer data.listPointer data.items data.payload.slotIndex) item.total
    (by decide) (by decide) (by decide) (Mpt.WitnessStep.original_code .resolve ready.code live.code)
  let entry:=callEntryStateHOLFinite ready callee
  have entryDatabase:=readyDatabase.of_frame (show LocalEffects.erase entry=LocalEffects.erase ready from rfl)
  have fits : (Rlp.Slices.itemPointer data.listPointer data.items data.payload.slotIndex).toNat+item.total.toNat<2^64:=
    beforeDb.trans_lt databaseData.table.isLt
  have bodyPrice:=resolve_body_cost databaseData entry _ item.total entryDatabase tableBefore dbLocal pointerLocal lengthLocal (live.of_frame rfl) fits
  have callPrice:=ClockCost.scoped_current ready (ofString "r") (.comb [.one,.one,.one,.one]) (ofString "_resolve_step") Mpt.WitnessCore.resolveArguments _
    (Mpt.WitnessStep.body .resolve) Mpt.WitnessCore.afterResolve callee (.comb [.one,.one,.one,.one])
    (60*item.total.toNat+281) 0 args called bodyPrice
    (ClockCost.of_quiet ready.code _ (Mpt.WitnessCore.after_resolve_quiet ready.code))
  rw [←Mpt.WitnessCore.resolve_call_shape] at callPrice
  have whole:=ClockCost.declared_current source "arr" Mpt.WitnessCore.resolveArray data.array Mpt.WitnessCore.resolveCall
    (60*item.total.toNat+282) arrayRead (callPrice.trans (by omega))
  rw [Mpt.WitnessCore.resolve_shape]
  exact whole.trans (by omega)

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Mpt.WitnessCore.after_resolve_quiet
#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.core_resolve_cost
