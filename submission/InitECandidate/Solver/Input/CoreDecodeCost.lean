import InitECandidate.Solver.Input.WitnessDecodeBodyCost
import InitECandidate.Solver.Mpt.WitnessCoreDecodeProgram
import InitECandidate.Solver.Input.WordTripleEnvironment

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang

theorem after_decode_quiet (code) : Input.QuietClock.Preserves code afterDecode := by
  rw [after_decode_shape,terminal_shape,push_shape]
  simp only [pushLink,pushTop,pushSlot,pushMode]
  repeat' first
    | apply Input.QuietClock.conditional
    | apply Input.QuietClock.sequence
    | exact Input.QuietClock.assign code _ _
    | exact Input.QuietClock.store code _ _

end InitECandidate.Solver.Mpt.WitnessCore

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The original core's complete decode-mode block, including its real
caller tick and every terminal/push/failed continuation outcome. Current
physical database/input/heap/scratch facts provide the actual callee entry. -/
theorem core_decode_cost (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length cursor limit : BitVec 64) (boundary : RootBoundary input source)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "cur_p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "cur_n")=some (.val (.word length)))
    (arena : Rlp.Validation.Arena source cursor limit)
    (before : pointer.toNat+length.toNat≤db.toNat) (small : length.toNat≤1024)
    (inputAbove : 2713731432≤pointer.toNat) (below : cursor.toNat≤2713717616)
    (installed : OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source Mpt.WitnessCore.decodeBranch).2.clock≤251*length.toNat+length.toNat/4+174 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) Mpt.WitnessCore.decodeArguments=
      some [.val (.word db),.val (.word pointer),.val (.word length)]:=by
    simp [Mpt.WitnessCore.decodeArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,dbCell,pointerCell,lengthCell]
  obtain ⟨callee,called,dbLocal,pointerLocal,lengthLocal⟩:=word_triple_environment source.code.lookup (ofString "_decode_step")
    (ofString "db") (ofString "p") (ofString "n") (Mpt.WitnessStep.body .decode) (.comb [.one,.one]) db pointer length
    (by decide) (by decide) (by decide) (Mpt.WitnessStep.original_code .decode source.code installed)
  let entry:=callEntryStateHOLFinite source callee
  have entryBoundary:=boundary.erase_frame input source entry rfl (dbLocal.trans dbCell.symm)
  have entryArena:=Rlp.Validation.Arena.of_fields source entry cursor limit arena rfl rfl
  have bodyPrice:=decode_body_cost input entry db pointer length cursor limit entryBoundary dbLocal pointerLocal lengthLocal entryArena before small inputAbove below installed
  have whole:=ClockCost.scoped_current source (ofString "d") (.comb [.one,.one]) (ofString "_decode_step") Mpt.WitnessCore.decodeArguments _
    (Mpt.WitnessStep.body .decode) Mpt.WitnessCore.afterDecode callee (.comb [.one,.one]) (251*length.toNat+length.toNat/4+173) 0 args called bodyPrice
    (ClockCost.of_quiet source.code _ (Mpt.WitnessCore.after_decode_quiet source.code))
  rw [Mpt.WitnessCore.decode_shape]
  exact whole.trans (by omega)

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Mpt.WitnessCore.after_decode_quiet
#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.core_decode_cost
