import InitECandidate.Solver.Arenas.Program

namespace InitECandidate.Solver.Arenas
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Complete successful execution of either actual arena allocator. It updates
only its own cursor global; the entire memory and FFI state are preserved.
The two real guards remain explicit until natural arena-room arithmetic is
supplied. No body clock or callee-success premise is assumed. -/
theorem execute {F : Type} (source : PanSemStateFiniteExact 64 F) (direction : Direction)
    (pointer limit amount : BitVec 64)
    (amountLocal : source.locals.lookup (ofString "n") = some (.val (.word amount)))
    (pointerGlobal : source.globals.lookup (ofString (pointerName direction)) = some (.val (.word pointer)))
    (limitGlobal : source.globals.lookup (ofString (limitName direction)) = some (.val (.word limit)))
    (fits : ¬ distance direction pointer limit < amount)
    (roundedFits : ¬ outside direction (rounded direction pointer amount) limit) :
    ∃ target : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState source (body direction) =
        (some (.returned (.val (.word (resultWord direction pointer amount)))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite (post source direction pointer amount) := by
  classical
  let pState := bind source "p" pointer
  let qState := bind pState "q" (rounded direction pointer amount)
  let changed := post qState direction pointer amount
  have pLocal : pState.locals.lookup (ofString "p") = some (.val (.word pointer)) := bind_lookup_same _ _ _
  have nLocal : pState.locals.lookup (ofString "n") = some (.val (.word amount)) :=
    (bind_lookup_other source "p" "n" _ (by decide)).trans amountLocal
  have qLocal : qState.locals.lookup (ofString "q") = some (.val (.word (rounded direction pointer amount))) := bind_lookup_same _ _ _
  have savedP : qState.locals.lookup (ofString "p") = some (.val (.word pointer)) :=
    (bind_lookup_other pState "q" "p" _ (by decide)).trans pLocal
  have limitP : pState.globals.lookup (ofString (limitName direction)) = some (.val (.word limit)) := limitGlobal
  have limitQ : qState.globals.lookup (ofString (limitName direction)) = some (.val (.word limit)) := limitGlobal
  have firstRun : evaluateHOLFiniteState pState (firstGuard direction) = (none, pState) := by
    rw [firstGuard, evaluateHOLFiniteState_ite]
    cases direction <;>
      simp only [distanceExpression, limitExpression, limitName, distance] at fits limitP ⊢ <;>
      simp [evalHOLExact, evalListHOLExact, toExact, localVar, pLocal, nLocal, limitP,
        valueIsWord, valueWord, wordOpHOL, wordOp, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, fits]
  have secondRun : evaluateHOLFiniteState qState (secondGuard direction) = (none, qState) := by
    rw [secondGuard, evaluateHOLFiniteState_ite]
    cases direction <;>
      simp only [secondTest, limitExpression, limitName, outside] at roundedFits limitQ ⊢ <;>
      simp [evalHOLExact, toExact, localVar, qLocal, limitQ,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, roundedFits]
  have assigned : evaluateHOLFiniteState qState (assignment direction) = (none, changed) := by
    rw [assignment, evaluateHOLFiniteState_assign]
    have pointerStored : qState.globals.lookup (ofString (pointerName direction)) = some (.val (.word pointer)) := pointerGlobal
    simp [localVar, evalHOLExact, toExact, qLocal, isValidValueHOLFinite, lookupKvarHOLFinite,
      pointerStored, shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite, changed, post]
  have returned : evaluateHOLFiniteState changed (.return (returnedExpression direction)) =
      (some (.returned (.val (.word (resultWord direction pointer amount)))), emptyLocalsHOLFinite changed) := by
    cases direction <;>
      simp [returnedExpression, resultWord, evaluateHOLFiniteState_return, localVar, evalHOLExact,
        toExact, changed, post, savedP, qLocal, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  have qRun : evaluateHOLFiniteState qState (qTail direction) =
      (some (.returned (.val (.word (resultWord direction pointer amount)))), emptyLocalsHOLFinite changed) := by
    rw [qTail, WitnessRadix.StateSteps.next_sequence qState qState _ _ secondRun (Nat.le_refl _),
      WitnessRadix.StateSteps.next_sequence qState changed _ _ assigned (Nat.le_refl _)]
    exact returned
  have qRead : eval pState (roundExpression direction) = some (.val (.word (rounded direction pointer amount))) := by
    cases direction <;>
      simp [eval, roundExpression, rounded, localVar, evalHOLExact, evalListHOLExact, toExact,
        pLocal, nLocal, valueIsWord, valueWord, wordOpHOL, wordOp, AndOp.and, BitVec.add_assoc]
  have qSetup : WitnessRadix.BuildEntry.Initializes pState [("q", roundExpression direction)] qState
      (fun output => restore pState "q" output) := .step _ qRead (.done _)
  have qScope := WitnessRadix.BuildEntry.declarations_execute qSetup (qTail direction)
  change evaluateHOLFiniteState pState (.dec (ofString "q") .one (roundExpression direction) (qTail direction)) = _ at qScope
  rw [qRun] at qScope
  have pRun : evaluateHOLFiniteState pState (pTail direction) =
      (some (.returned (.val (.word (resultWord direction pointer amount)))), restore pState "q" (emptyLocalsHOLFinite changed)) := by
    rw [pTail, WitnessRadix.StateSteps.next_sequence pState pState _ _ firstRun (Nat.le_refl _)]
    exact qScope
  have pRead : eval source (pointerExpression direction) = some (.val (.word pointer)) := by
    simp [eval, pointerExpression, evalHOLExact, toExact, pointerGlobal]
  have pSetup : WitnessRadix.BuildEntry.Initializes source [("p", pointerExpression direction)] pState
      (fun output => restore source "p" output) := .step _ pRead (.done _)
  have pScope := WitnessRadix.BuildEntry.declarations_execute pSetup (pTail direction)
  change evaluateHOLFiniteState source (program direction) = _ at pScope
  rw [pRun] at pScope
  let target := restore source "p" (restore pState "q" (emptyLocalsHOLFinite changed))
  refine ⟨target, ?_, rfl⟩
  rw [body_shape]
  exact pScope

end InitECandidate.Solver.Arenas

#print axioms InitECandidate.Solver.Arenas.execute
