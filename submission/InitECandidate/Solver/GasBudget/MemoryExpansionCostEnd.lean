import InitECandidate.Solver.GasBudget.MemoryExpansionCostRounded
import InitECandidate.Solver.Input.NormalDeclarationEntry

namespace InitECandidate.Solver.GasBudget.MemoryExpansionCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem end_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame current endp : BitVec 64)
    (view : View source frame current)
    (endLocal : source.locals.lookup (ofString "endp") = some (.val (.word endp)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterEnd = (some (.returned returned), post)) :
    returned = pairValue (endPair current endp) := by
  by_cases maximum : endp = 18446744073709551615#64
  · have guarded : evaluateHOLFiniteState source (maxGuard "endp") =
        (some (.returned (pairValue (18446744073709551615#64, 0#64))), emptyLocalsHOLFinite source) := by
      simp [maxGuard, returnMax, pairExpression, pairValue, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_return,
        evalHOLExact, evalListHOLExact, toExact, localVar, endLocal, maximum, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
        shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [afterEnd, WitnessRadix.StateSteps.stopped_sequence source _ (maxGuard "endp") _ _ guarded (Nat.le_refl _)] at normal
    rw [endPair, if_pos maximum]
    exact PanSemResultExact.returned.inj (Option.some.inj (congrArg Prod.fst normal).symm)
  · have guarded : evaluateHOLFiniteState source (maxGuard "endp") = (none, source) := by
      simp [maxGuard, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_skip, evalHOLExact, toExact, localVar,
        endLocal, maximum, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    rw [afterEnd, WitnessRadix.StateSteps.next_sequence source source (maxGuard "endp") _ guarded (Nat.le_refl _)] at normal
    obtain ⟨curValue, inner, read, typed, run, scopeEq⟩ := Input.CallNormal.declaration_normal_entry source post "cur" .one (frameLoad 32#64) afterCurrent returned normal
    have expected := frame_read source frame 32#64 current view.ev view.mapped view.cell
    have curEq : curValue = .val (.word current) := Option.some.inj (read.symm.trans expected)
    subst curValue
    let ready := WitnessRadix.QueryBranch.bind source "cur" current
    have currentLocal : ready.locals.lookup (ofString "cur") = some (.val (.word current)) := bind_lookup_same _ _ _
    have readyEnd : ready.locals.lookup (ofString "endp") = some (.val (.word endp)) :=
      (bind_lookup_other _ "cur" "endp" _ (by decide)).trans endLocal
    rw [endPair, if_neg maximum]
    exact rounded_normal ready inner current endp view.installed currentLocal readyEnd returned run

end InitECandidate.Solver.GasBudget.MemoryExpansionCost

#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost.end_normal
