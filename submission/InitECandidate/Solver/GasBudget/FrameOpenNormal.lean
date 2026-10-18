import InitECandidate.Solver.GasBudget.FrameOpenCall
import InitECandidate.Solver.ClockPadding
import InitECandidate.Solver.Input.NormalCallClock

namespace InitECandidate.Solver.GasBudget.FrameOpen
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A reached normal frame_open body derives its real clock payment and
fresh active regular ledger. The constructive constructor is funded only
by temporary clock padding, which exact non-timeout equality removes. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (scratch lower message empty parent continuation kind : BitVec 64) (words : FrameNew.MessageWords)
    (addresses keys addressCount keyCount : BitVec 64)
    (entry : FrameNew.Entry source scratch lower message empty words addresses keys addressCount keyCount)
    (known : source.code.lookup (ofString "frame_new") = some (FrameNew.formals, FrameNew.body, .one))
    (messageLocal : source.locals.lookup (ofString "msg") = some (.val (.word message)))
    (kindLocal : source.locals.lookup (ofString "kind") = some (.val (.word kind)))
    (evGlobal : source.globals.lookup (ofString "ev") = some (.val (.word parent)))
    (continuationGlobal : source.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (room : lower.toNat + JumpDest.bitmapBytes words.length.toNat + 2760 ≤ scratch.toNat)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value), target)) :
    ∃ spent, spent ≤ words.length.toNat ∧
      WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 44 + spent ≤ source.clock ∧
      value = .val (.word (FrameNew.framePointer scratch)) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with
        globals := (((source.globals.update (ofString "frame_mem_ptr", .val (.word (FrameNew.memoryPointer lower)))).update
          (ofString "scratch_ptr", .val (.word (recordPointer (FrameNew.finalScratch scratch words.length))))).update
          (ofString "ev", .val (.word (FrameNew.framePointer scratch)))).update
          (ofString "cur_cont", .val (.word (recordPointer (FrameNew.finalScratch scratch words.length))))
        memory := target.memory
        clock := source.clock - (WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 44 + spent)} ∧
      regularBudget target.memory (FrameNew.framePointer scratch) = words.gas.toNat ∧
      ∀ query, Arenas.Outside lower scratch query → target.memory query = source.memory query := by
  let extra := words.length.toNat + WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 44
  let padded := {source with clock := source.clock + extra}
  have paddedEntry : FrameNew.Entry padded scratch lower message empty words addresses keys addressCount keyCount :=
    entry.relocals_clock source.locals (source.clock + extra)
  obtain ⟨checked, spent, bound, actual, frame, budget, outside⟩ := execute padded scratch lower message empty parent continuation kind words
    addresses keys addressCount keyCount paddedEntry known messageLocal kindLocal evGlobal continuationGlobal room
      (by change extra ≤ source.clock + extra; omega)
  have lifted := panPropsEvaluateAddClockEq body source (some (.returned value)) target extra ⟨normal, by intro impossible; cases impossible⟩
  have same := lifted.symm.trans actual
  have valueEq : value = .val (.word (FrameNew.framePointer scratch)) := by
    simpa only [Prod.mk.injEq, Option.some.injEq, PanSemResultExact.returned.injEq] using (congrArg Prod.fst same)
  have targetEq := congrArg Prod.snd same
  change {target with clock := target.clock + extra} = checked at targetEq
  rw [← targetEq] at frame budget outside
  have stripped := InitECandidate.Solver.strip_clock_padding source target
    {source with
      globals := (((source.globals.update (ofString "frame_mem_ptr", .val (.word (FrameNew.memoryPointer lower)))).update
        (ofString "scratch_ptr", .val (.word (recordPointer (FrameNew.finalScratch scratch words.length))))).update
        (ofString "ev", .val (.word (FrameNew.framePointer scratch)))).update
        (ofString "cur_cont", .val (.word (recordPointer (FrameNew.finalScratch scratch words.length))))
      memory := target.memory}
    (WitnessRadix.Zero.price (JumpDest.bitmapBytes words.length.toNat) + 44 + spent) extra (by dsimp [extra]; omega) frame
  exact ⟨spent, bound, stripped.1, valueEq, stripped.2, budget, outside⟩

end InitECandidate.Solver.GasBudget.FrameOpen

#print axioms InitECandidate.Solver.GasBudget.FrameOpen.body_normal
