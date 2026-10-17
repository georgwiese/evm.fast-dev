import InitECandidate.Solver.GasBudget.RootProgram
import InitECandidate.Solver.WitnessRadix.BindingLookup

namespace InitECandidate.Solver.GasBudget.RootBudget
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

noncomputable def initial (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (gas intrinsic regular : BitVec 64) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  bind (bind source "execution_gas" (executionWord gas intrinsic)) "regular_budget" (regularWord regular)
noncomputable def afterMinimum (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (gas intrinsic regular : BitVec 64) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  bind { initial source gas intrinsic regular with clock := source.clock - 1 }
    "mgas" (liquidWord gas intrinsic regular)
noncomputable def entered (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (gas intrinsic regular : BitVec 64) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  bind (afterMinimum source gas intrinsic regular) "reservoir" (reservoirWord gas intrinsic regular)
noncomputable def closeScope (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (gas intrinsic regular : BitVec 64) (target : PanSemStateFiniteExact 64 Guest.HostMemory) :
    PanSemStateFiniteExact 64 Guest.HostMemory :=
  restore source "execution_gas"
    (restore (bind source "execution_gas" (executionWord gas intrinsic)) "regular_budget"
      (restore (initial source gas intrinsic regular) "mgas"
        (restore (afterMinimum source gas intrinsic regular) "reservoir" target)))

/-- Execute the real four-declaration split and its real min call. The exact
lexical restorations surround an arbitrary subsequent transaction body. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (gas intrinsic regular state floor : BitVec 64)
    (gasLocal : source.locals.lookup (ofString "gas") = some (.val (.word gas)))
    (totalLocal : source.locals.lookup (ofString "intrinsic_gas") = some (.val (.word intrinsic)))
    (intrinsicLocal : source.locals.lookup (ofString "intrinsic") = some (intrinsicValue regular state floor))
    (code : source.code.lookup (ofString "min") = some (Minimum.formals, Minimum.body, .one))
    (enough : 1 ≤ source.clock) (continuation : ProgHOL 64) :
    evaluateHOLFiniteState source (program continuation) =
      (let output := evaluateHOLFiniteState (entered source gas intrinsic regular) continuation
       (output.1, closeScope source gas intrinsic regular output.2)) := by
  classical
  have executionRead : eval source executionExpression = some (.val (.word (executionWord gas intrinsic))) := by
    simp [eval, executionExpression, executionWord, localVar, evalHOLExact, evalListHOLExact, toExact,
      gasLocal, totalLocal, valueIsWord, valueWord, wordOpHOL, wordOp]
  have regularRead : eval (bind source "execution_gas" (executionWord gas intrinsic)) regularExpression =
      some (.val (.word (regularWord regular))) := by
    have stored := (bind_lookup_other source "execution_gas" "intrinsic" (executionWord gas intrinsic) (by decide)).trans intrinsicLocal
    simp [eval, regularExpression, regularWord, intrinsicValue, localVar, evalHOLExact,
      evalListHOLExact, toExact, stored, valueIsWord, valueWord, wordOpHOL, wordOp]
  have setup : WitnessRadix.BuildEntry.Initializes source
      [("execution_gas", executionExpression), ("regular_budget", regularExpression)]
      (initial source gas intrinsic regular)
      (fun target => restore source "execution_gas"
        (restore (bind source "execution_gas" (executionWord gas intrinsic)) "regular_budget" target)) :=
    .step (executionWord gas intrinsic) executionRead (.step (regularWord regular) regularRead (.done _))
  have args : evalListHOLFinite (initial source gas intrinsic regular)
      (h := fun address => Classical.propDecidable ((initial source gas intrinsic regular).memaddrs address)) minArguments =
      some [.val (.word (regularWord regular)), .val (.word (executionWord gas intrinsic))] := by
    simp [minArguments, initial, evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar,
      WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString]
  have reservoirRead : eval (afterMinimum source gas intrinsic regular) reservoirExpression =
      some (.val (.word (reservoirWord gas intrinsic regular))) := by
    simp [eval, afterMinimum, initial, reservoirExpression, reservoirWord, localVar, evalHOLExact,
      evalListHOLExact, toExact, WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      ofString, valueIsWord, valueWord, wordOpHOL, wordOp]
  have reservoirSetup : WitnessRadix.BuildEntry.Initializes (afterMinimum source gas intrinsic regular)
      [("reservoir", reservoirExpression)] (entered source gas intrinsic regular)
      (fun target => restore (afterMinimum source gas intrinsic regular) "reservoir" target) :=
    .step (reservoirWord gas intrinsic regular) reservoirRead (.done _)
  have outer := WitnessRadix.BuildEntry.declarations_execute setup
    (.decCall (ofString "mgas") .one (ofString "min") minArguments
      (.dec (ofString "reservoir") .one reservoirExpression continuation))
  have called := Minimum.call_execute (initial source gas intrinsic regular)
    (regularWord regular) (executionWord gas intrinsic) "mgas" minArguments
    (.dec (ofString "reservoir") .one reservoirExpression continuation) args code enough
  have final := WitnessRadix.BuildEntry.declarations_execute reservoirSetup continuation
  change evaluateHOLFiniteState (afterMinimum source gas intrinsic regular)
    (.dec (ofString "reservoir") .one reservoirExpression continuation) = _ at final
  change evaluateHOLFiniteState source (program continuation) = _ at outer
  rw [outer, called]
  change (let output := (evaluateHOLFiniteState (afterMinimum source gas intrinsic regular)
      (.dec (ofString "reservoir") .one reservoirExpression continuation));
    (output.1, restore source "execution_gas"
      (restore (bind source "execution_gas" (executionWord gas intrinsic)) "regular_budget"
        (restore (initial source gas intrinsic regular) "mgas" output.2)))) = _
  rw [final]
  rfl

theorem entered_fields (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (gas intrinsic regular : BitVec 64) :
    (entered source gas intrinsic regular).memory = source.memory ∧
    (entered source gas intrinsic regular).globals = source.globals ∧
    (entered source gas intrinsic regular).ffi = source.ffi ∧
    (entered source gas intrinsic regular).clock = source.clock - 1 ∧
    (entered source gas intrinsic regular).locals.lookup (ofString "mgas") =
      some (.val (.word (liquidWord gas intrinsic regular))) ∧
    (entered source gas intrinsic regular).locals.lookup (ofString "reservoir") =
      some (.val (.word (reservoirWord gas intrinsic regular))) := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (bind_lookup_other _ "reservoir" "mgas" _ (by decide)).trans (bind_lookup_same _ _ _)
  · exact bind_lookup_same _ _ _

end InitECandidate.Solver.GasBudget.RootBudget

#print axioms InitECandidate.Solver.GasBudget.RootBudget.execute
#print axioms InitECandidate.Solver.GasBudget.RootBudget.entered_fields
