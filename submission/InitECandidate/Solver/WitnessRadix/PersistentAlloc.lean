import InitECandidate.Solver.WitnessRadix.Copy32Execution

namespace InitECandidate.Solver.WitnessRadix.PersistentAlloc
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_alloc with
  | .function fn => progToHOL fn.body | _ => .skip
def heapEnd : BitVec 64 := 33806089496#64
def rounded (pointer amount : BitVec 64) : BitVec 64 := (pointer + amount + 7#64) &&& (0#64 - 8#64)
def post {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer amount : BitVec 64) :
    PanSemStateFiniteExact 64 F :=
  { source with globals := source.globals.update (ofString "heap_ptr", .val (.word (rounded pointer amount))) }

def heapVar : ExpHOL 64 := .var .global (ofString "heap_ptr")
def roundExpression : ExpHOL 64 := .op .and
  [.op .add [localVar "p", localVar "n", .const 7#64], .op .sub [.const 0#64, .const 8#64]]
def trap : ProgHOL 64 := .call (some (none, none)) (ofString "trap_with") [.const 1#64]
def firstGuard : ProgHOL 64 :=
  .ite (.cmp .lower (.op .sub [.const heapEnd, localVar "p"]) (localVar "n")) trap .skip
def secondGuard : ProgHOL 64 := .ite (.cmp .lower (.const heapEnd) (localVar "q")) trap .skip
def assignment : ProgHOL 64 := .assign .global (ofString "heap_ptr") (localVar "q")
def returnPointer : ProgHOL 64 := .return (localVar "p")
def qTail : ProgHOL 64 := .seq secondGuard (.seq assignment returnPointer)
def pTail : ProgHOL 64 := .seq firstGuard (.dec (ofString "q") .one roundExpression qTail)

theorem body_shape : body = .dec (ofString "p") .one heapVar pTail := by
  simp only [body, Guest.guestFn_alloc, progToHOL, expToHOL, shapeToHOL,
    heapVar, pTail, qTail, firstGuard, secondGuard, trap, assignment, returnPointer,
    roundExpression, heapEnd, localVar, List.map_cons, List.map_nil, Option.map_none]

/-- Complete successful fixed persistent allocator; no body clock is paid. -/
theorem execute {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer amount : BitVec 64)
    (amountLocal : source.locals.lookup (ofString "n") = some (.val (.word amount)))
    (heapGlobal : source.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (fits : ¬ heapEnd - pointer < amount) (roundedFits : ¬ heapEnd < rounded pointer amount) :
    ∃ target : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState source body = (some (.returned (.val (.word pointer))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite (post source pointer amount) := by
  classical
  let pState := bind source "p" pointer
  let qState := bind pState "q" (rounded pointer amount)
  let changed := post qState pointer amount
  have pLocal : pState.locals.lookup (ofString "p") = some (.val (.word pointer)) := bind_lookup_same _ _ _
  have nLocal : pState.locals.lookup (ofString "n") = some (.val (.word amount)) :=
    (bind_lookup_other source "p" "n" _ (by decide)).trans amountLocal
  have qLocal : qState.locals.lookup (ofString "q") = some (.val (.word (rounded pointer amount))) := bind_lookup_same _ _ _
  have savedP : qState.locals.lookup (ofString "p") = some (.val (.word pointer)) :=
    (bind_lookup_other pState "q" "p" _ (by decide)).trans pLocal
  have firstRun : evaluateHOLFiniteState pState firstGuard = (none, pState) := by
    rw [firstGuard, evaluateHOLFiniteState_ite]
    simp [evalHOLExact, evalListHOLExact, toExact, localVar, pLocal, nLocal, valueIsWord, valueWord,
      wordOpHOL, wordOp, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, fits]
  have secondRun : evaluateHOLFiniteState qState secondGuard = (none, qState) := by
    rw [secondGuard, evaluateHOLFiniteState_ite]
    simp [evalHOLExact, toExact, localVar, qLocal, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, roundedFits]
  have assigned : evaluateHOLFiniteState qState assignment = (none, changed) := by
    rw [assignment, evaluateHOLFiniteState_assign]
    have heap : qState.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)) := heapGlobal
    simp [localVar, evalHOLExact, toExact, qLocal, isValidValueHOLFinite, lookupKvarHOLFinite,
      heap, shapeOfHOLExact, shapeEqHOL, setKvarHOLFinite, setGlobalHOLFinite, changed, post]
  have returned : evaluateHOLFiniteState changed returnPointer =
      (some (.returned (.val (.word pointer))), emptyLocalsHOLFinite changed) := by
    simp [returnPointer, evaluateHOLFiniteState_return, localVar, evalHOLExact, toExact, changed, post,
      savedP, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  have qRun : evaluateHOLFiniteState qState qTail =
      (some (.returned (.val (.word pointer))), emptyLocalsHOLFinite changed) := by
    rw [qTail, StateSteps.next_sequence qState qState _ _ secondRun (Nat.le_refl _),
      StateSteps.next_sequence qState changed _ _ assigned (Nat.le_refl _)]
    exact returned
  have qRead : eval pState roundExpression = some (.val (.word (rounded pointer amount))) := by
    simp [eval, roundExpression, rounded, localVar, evalHOLExact, evalListHOLExact, toExact,
      pLocal, nLocal, valueIsWord, valueWord, wordOpHOL, wordOp, AndOp.and, BitVec.add_assoc]
  have qSetup : BuildEntry.Initializes pState [("q", roundExpression)] qState
      (fun output => restore pState "q" output) := .step _ qRead (.done _)
  have qScope := BuildEntry.declarations_execute qSetup qTail
  change evaluateHOLFiniteState pState (.dec (ofString "q") .one roundExpression qTail) = _ at qScope
  rw [qRun] at qScope
  have pRun : evaluateHOLFiniteState pState pTail =
      (some (.returned (.val (.word pointer))), restore pState "q" (emptyLocalsHOLFinite changed)) := by
    rw [pTail, StateSteps.next_sequence pState pState _ _ firstRun (Nat.le_refl _)]
    exact qScope
  have pRead : eval source heapVar = some (.val (.word pointer)) := by
    simp [eval, heapVar, evalHOLExact, toExact, heapGlobal]
  have pSetup : BuildEntry.Initializes source [("p", heapVar)] pState
      (fun output => restore source "p" output) := .step _ pRead (.done _)
  have pScope := BuildEntry.declarations_execute pSetup pTail
  change evaluateHOLFiniteState source (.dec (ofString "p") .one heapVar pTail) = _ at pScope
  rw [pRun] at pScope
  let target := restore source "p" (restore pState "q" (emptyLocalsHOLFinite changed))
  refine ⟨target, ?_, rfl⟩
  rw [body_shape]
  exact pScope

end InitECandidate.Solver.WitnessRadix.PersistentAlloc

#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.execute
