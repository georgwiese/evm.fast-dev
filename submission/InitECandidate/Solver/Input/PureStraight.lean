import InitECandidate.Solver.Input.ReturnNormal
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.Input.PureStraight
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
variable {F : Type}

def Returns (source : PanSemStateFiniteExact 64 F) (program : ProgHOL 64) (value : ValueHOL 64) : Prop :=
  ∃ target, evaluateHOLFiniteState source program = (some (.returned value), target) ∧ emptyLocalsHOLFinite target = emptyLocalsHOLFinite source

theorem declares {source : PanSemStateFiniteExact 64 F} {name : MlS} {shape : ShapeHOL}
    {expression : ExpHOL 64} {continuation : ProgHOL 64} {returned : ValueHOL 64} (declared : ValueHOL 64)
    (read : eval source expression = some declared) (typed : shapeEqHOL shape (shapeOfHOLExact declared) = true)
    (next : Returns (setVarHOLFinite name declared source) continuation returned) :
    Returns source (.dec name shape expression continuation) returned := by
  classical
  obtain ⟨target, run, frame⟩ := next
  let restored := {target with locals := HolFiniteMapExact.resVarEq target.locals (name, source.locals.lookup name)}
  refine ⟨restored, ?_, frame⟩
  simp only [eval] at read
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  simp only [read, typed, ↓reduceIte]
  change (let output := evaluateHOLFiniteState (setVarHOLFinite name declared source) continuation
    (output.1, {output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (name, source.locals.lookup name)})) = _
  rw [run]

theorem command {source middle : PanSemStateFiniteExact 64 F} {program continuation : ProgHOL 64} {returned : ValueHOL 64}
    (run : evaluateHOLFiniteState source program = (none, middle))
    (frame : emptyLocalsHOLFinite middle = emptyLocalsHOLFinite source)
    (next : Returns middle continuation returned) : Returns source (.seq program continuation) returned := by
  obtain ⟨target, finished, fields⟩ := next
  have clock := congrArg PanSemStateFiniteExact.clock frame
  change middle.clock = source.clock at clock
  refine ⟨target, ?_, fields.trans frame⟩
  rw [WitnessRadix.StateSteps.next_sequence _ _ _ _ run (by omega)]
  exact finished

theorem carry_value (a b c : BitVec 64) :
    panPrimopHOLExact .addCarry [.val (.word a), .val (.word b), .val (.word c)] =
      some (.rStruct [.val (.word (wordAddCarryHOL a b c).1), .val (.word (wordAddCarryHOL a b c).2)]) := by
  simp only [panPrimopHOLExact]

theorem carry {source : PanSemStateFiniteExact 64 F} {name : MlS} {arguments : List (ExpHOL 64)}
    {continuation : ProgHOL 64} {returned : ValueHOL 64} (a b c : BitVec 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments =
      some [.val (.word a), .val (.word b), .val (.word c)])
    (existing : source.locals.lookup name = some (.rStruct [.val (.word 0#64), .val (.word 0#64)]))
    (next : Returns (setVarHOLFinite name (.rStruct [.val (.word (wordAddCarryHOL a b c).1), .val (.word (wordAddCarryHOL a b c).2)]) source) continuation returned) :
    Returns source (.seq (.primitive name .addCarry arguments) continuation) returned := by
  classical
  have valid : isValidValueHOLFinite source .local name
      (.rStruct [.val (.word (wordAddCarryHOL a b c).1), .val (.word (wordAddCarryHOL a b c).2)]) = true := by
    simp [isValidValueHOLFinite, lookupKvarHOLFinite, existing, shapeOfHOLExact, shapeEqHOL_eq_true]
  have step : evaluateHOLFiniteState source (.primitive name .addCarry arguments) =
      (none, setVarHOLFinite name (.rStruct [.val (.word (wordAddCarryHOL a b c).1), .val (.word (wordAddCarryHOL a b c).2)]) source) := by
    change evalListHOLExact source.toExact arguments = some [.val (.word a), .val (.word b), .val (.word c)] at args
    rw [evaluateHOLFiniteState_primitive]
    simp only [args, carry_value, valid, ↓reduceIte]
  exact command step rfl next

end InitECandidate.Solver.Input.PureStraight

#print axioms InitECandidate.Solver.Input.PureStraight.declares
#print axioms InitECandidate.Solver.Input.PureStraight.command
#print axioms InitECandidate.Solver.Input.PureStraight.carry
