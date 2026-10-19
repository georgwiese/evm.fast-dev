import InitECandidate.Solver.Input.CounterFlow

namespace InitECandidate.Solver.Input.CounterFlow
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem declared (key name : MlS) (shape : ShapeHOL) (expression : ExpHOL 64) (body : ProgHOL 64) (amount : Nat)
    (other : key ≠ name) (tail : Advances key amount body) :
    Advances key amount (.dec name shape expression body) := by
  classical
  intro source post word cell run
  rw [evaluateHOLFiniteState_dec_total] at run
  simp only at run
  split at run
  · cases run
  · rename_i value read
    split at run
    · let entry := setVarHOLFinite name value source
      have entryCell : entry.locals.lookup key = some (.val (.word word)) := by
        simpa [entry, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, other, Ne.symm other] using cell
      generalize computed : evaluateHOLFiniteState entry body = output at run
      obtain ⟨result, inner⟩ := output
      have resultEq : result = none := congrArg Prod.fst run
      have actual : evaluateHOLFiniteState entry body = (none, inner) := by rw [computed, resultEq]
      have postEq := congrArg Prod.snd run
      change {inner with locals := inner.locals.resVarEq (name, source.locals.lookup name)} = post at postEq
      have next := tail entry inner word entryCell actual
      rw [← postEq]
      change (inner.locals.resVarEq (name, source.locals.lookup name)).lookup key = _
      rw [lookup_resVarEq_toExact]
      cases saved : source.locals.lookup name <;> simpa [resVarHOLExact, FUPDATE, FDOMSUB, other] using next
    · cases run

end InitECandidate.Solver.Input.CounterFlow

#print axioms InitECandidate.Solver.Input.CounterFlow.declared
