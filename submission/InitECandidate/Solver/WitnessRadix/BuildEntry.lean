import InitECandidate.Solver.WitnessRadix.BuildProgram
import InitECandidate.Solver.WitnessRadix.QueryBranchStep

namespace InitECandidate.Solver.WitnessRadix.BuildEntry
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

def multiply (expression : ExpHOL 64) (factor : BitVec 64) : ExpHOL 64 :=
  .panop .mul [expression, .const factor]
def header (offset : BitVec 64) : ExpHOL 64 := .load .one (addConst (localVar "t") offset)
def suffix (name : String) (scale : BitVec 64) : ExpHOL 64 :=
  .op .add [localVar name, multiply (localVar "n") scale]

def bindings : List (String × ExpHOL 64) :=
  [("keys", header 32#64), ("vals", header 40#64), ("src", header 56#64), ("dst", header 64#64),
   ("pending_start", suffix "src" 8#64), ("pending_count", suffix "dst" 8#64),
   ("pending_node", suffix "vals" 8#64), ("node_next", suffix "keys" 32#64),
   ("dest", addConst (localVar "t") 24#64), ("start", .const 0#64),
   ("count", localVar "n"), ("bit", .const 0#64), ("depth", .const 0#64)]

def declarations : List (String × ExpHOL 64) → ProgHOL 64 → ProgHOL 64
  | [], continuation => continuation
  | (name, expression) :: rest, continuation =>
      .dec (ofString name) .one expression (declarations rest continuation)

def stripDeclarations : ProgHOL 64 → ProgHOL 64
  | .dec _ _ _ rest => stripDeclarations rest
  | code => code
def core : ProgHOL 64 := stripDeclarations BuildProgram.body
def mainLoop : ProgHOL 64 := (BuildProgram.loops BuildProgram.body)[0]?.getD .skip
def mainBody : ProgHOL 64 := match mainLoop with | .while _ body => body | _ => .skip
def returnZero : ProgHOL 64 := .return (.const 0#64)

theorem body_shape : BuildProgram.body = declarations bindings core := by
  simp only [BuildProgram.body, RawProgram.guestFn_solver_radix_index, bindings, core,
    stripDeclarations, declarations, header, suffix, multiply, localVar, addConst,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil]

theorem core_shape : core =
    .seq (.ite (.cmp .equal (localVar "n") (.const 0#64))
      (.seq (.store (localVar "dest") (.const 0#64)) returnZero) .skip)
      (.seq mainLoop returnZero) := by
  simp only [core, stripDeclarations, BuildProgram.body, RawProgram.guestFn_solver_radix_index,
    mainLoop, BuildProgram.loops, returnZero, localVar, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, List.nil_append, List.cons_append, List.append_nil,
    List.getElem?_cons_zero, Option.getD_some]

/-- Entry prefix evidence consists only of actual expression evaluations.
It records all lexical restorations needed after the body returns. -/
inductive Initializes {F : Type} : PanSemStateFiniteExact 64 F → List (String × ExpHOL 64) →
    PanSemStateFiniteExact 64 F → (PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F) → Prop
  | done (source) : Initializes source [] source id
  | step {source entered name expression rest restoreRest} (word : BitVec 64)
      (read : eval source expression = some (.val (.word word)))
      (next : Initializes (bind source name word) rest entered restoreRest) :
      Initializes source ((name, expression) :: rest) entered
        (fun output => restore source name (restoreRest output))

theorem declarations_execute {F : Type} {source entered : PanSemStateFiniteExact 64 F}
    {bindings : List (String × ExpHOL 64)}
    {restoreStack : PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F}
    (setup : Initializes source bindings entered restoreStack) (continuation : ProgHOL 64) :
    evaluateHOLFiniteState source (declarations bindings continuation) =
      (let output := evaluateHOLFiniteState entered continuation;
       (output.1, restoreStack output.2)) := by
  classical
  induction setup with
  | done source => rfl
  | @step source entered name expression rest restoreRest word read next ih =>
      simp only [eval] at read
      rw [declarations, evaluateHOLFiniteState_dec_total]
      simp only [read, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
      change (let output := evaluateHOLFiniteState (bind source name word) (declarations rest continuation);
        (output.1, restore source name output.2)) = _
      rw [ih]

theorem initialization_frame {F : Type} {source entered : PanSemStateFiniteExact 64 F}
    {bindings : List (String × ExpHOL 64)}
    {restoreStack : PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F}
    (setup : Initializes source bindings entered restoreStack) :
    emptyLocalsHOLFinite entered = emptyLocalsHOLFinite source := by
  induction setup with
  | done source => rfl
  | step word read next ih => exact ih

theorem restoration_frame {F : Type} {source entered : PanSemStateFiniteExact 64 F}
    {bindings : List (String × ExpHOL 64)}
    {restoreStack : PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F}
    (setup : Initializes source bindings entered restoreStack) (output : PanSemStateFiniteExact 64 F) :
    emptyLocalsHOLFinite (restoreStack output) = emptyLocalsHOLFinite output := by
  induction setup with
  | done source => rfl
  | step word read next ih => exact ih

end InitECandidate.Solver.WitnessRadix.BuildEntry

#print axioms InitECandidate.Solver.WitnessRadix.BuildEntry.body_shape
#print axioms InitECandidate.Solver.WitnessRadix.BuildEntry.core_shape
#print axioms InitECandidate.Solver.WitnessRadix.BuildEntry.declarations_execute
