import InitECandidate.Solver.Mpt.CurrentWitnessDecodeStep
import InitECandidate.Solver.Mpt.WitnessCoreTerminal
import InitECandidate.Solver.Input.WordTripleEnvironment
import InitECandidate.Solver.Input.ClockCostScopedReached

namespace InitECandidate.Solver.Mpt.WitnessCore
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The actual terminal and record-push tails contain only reads, stores
and local assignments. They spend zero source call/loop ticks on every
outcome; their straight-line target work must still be counted separately. -/
theorem after_decode_price (code) : ClockCost.Bound code afterDecode 0 := by
  rw [after_decode_shape,terminal_shape,push_shape]
  simp only [pushLink,pushTop,pushSlot,pushMode]
  repeat first
    | apply ClockCost.sequence _ _ _ 0 0
    | apply ClockCost.conditional _ _ _ _ 0 0
    | exact ClockCost.store _ _ _
    | exact ClockCost.assign _ _ _

theorem current_decode_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (db pointer length : BitVec 64)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "cur_p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "cur_n")=some (.val (.word length))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) decodeArguments=
      some [.val (.word db),.val (.word pointer),.val (.word length)] := by
  simp [decodeArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,dbCell,pointerCell,lengthCell]

theorem current_decode_environment (source : PanSemStateFiniteExact 64 Guest.HostMemory) (db pointer length : BitVec 64)
    (installed : OriginalCode.Installed source.code) :
    ∃ callee,lookupCodeHOLFinite source.code.lookup (ofString "_decode_step") [.val (.word db),.val (.word pointer),.val (.word length)]=
      some (WitnessStep.body .decode,callee,.comb [.one,.one]) ∧
      callee.lookup (ofString "db")=some (.val (.word db)) ∧ callee.lookup (ofString "p")=some (.val (.word pointer)) ∧
      callee.lookup (ofString "n")=some (.val (.word length)) :=
  word_triple_environment source.code.lookup (ofString "_decode_step") (ofString "db") (ofString "p") (ofString "n")
    (WitnessStep.body .decode) (.comb [.one,.one]) db pointer length (by decide) (by decide) (by decide)
    (WitnessStep.original_code .decode source.code installed)

/-- Both genuine decode outcomes have the same straight-line caller
allowance. Pending pushes and failed reads/stores are included. -/
theorem current_decode_branch_price (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap : BitVec 64)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "cur_p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "cur_n")=some (.val (.word length)))
    (small : length.toNat≤1024) (before : pointer.toNat+length.toNat≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : Rlp.LiveArena source) :
    source.clock-(evaluateHOLFiniteState source decodeBranch).2.clock≤length.toNat/4+251*length.toNat+285 := by
  obtain ⟨callee,called,dbLocal,pointerLocal,lengthLocal⟩:=current_decode_environment source db pointer length arena.code
  rw [decode_shape]
  have price:=ClockCost.scoped_reached_current source "d" (.comb [.one,.one]) (ofString "_decode_step") decodeArguments _
    (WitnessStep.body .decode) afterDecode callee (.comb [.one,.one]) (length.toNat/4+251*length.toNat+284) 0
    (current_decode_arguments source db pointer length dbCell pointerCell lengthCell) called
    (WitnessDecode.current_step_price (callEntryStateHOLFinite source callee) db pointer length heap dbLocal pointerLocal lengthLocal small before heapCell heapArena heapBound aligned (arena.of_frame rfl))
    (by
      intro target value normal checked
      exact after_decode_price target.code (CallNormal.continuationEntry source target "d" value) rfl)
  exact Nat.le_trans price (by omega)


end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.after_decode_price
#print axioms InitECandidate.Solver.Mpt.WitnessCore.current_decode_branch_price
