import InitECandidate.Solver.WitnessRadix.PersistentAlloc

namespace InitECandidate.Solver.Arenas
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

inductive Direction where | up | down
  deriving DecidableEq

def pointerName : Direction → String | .up => "frame_mem_ptr" | .down => "scratch_ptr"
def limitName : Direction → String | .up => "scratch_ptr" | .down => "frame_mem_ptr"
def pointerExpression (direction : Direction) : ExpHOL 64 := .var .global (ofString (pointerName direction))
def limitExpression (direction : Direction) : ExpHOL 64 := .var .global (ofString (limitName direction))
def rounded : Direction → BitVec 64 → BitVec 64 → BitVec 64
  | .up, pointer, amount => (pointer + amount + 7#64) &&& (0#64 - 8#64)
  | .down, pointer, amount => (pointer - amount) &&& (0#64 - 8#64)
def roundExpression : Direction → ExpHOL 64
  | .up => .op .and [.op .add [localVar "p", localVar "n", .const 7#64], .op .sub [.const 0#64, .const 8#64]]
  | .down => .op .and [.op .sub [localVar "p", localVar "n"], .op .sub [.const 0#64, .const 8#64]]
def distance : Direction → BitVec 64 → BitVec 64 → BitVec 64
  | .up, pointer, limit => limit - pointer
  | .down, pointer, limit => pointer - limit
def distanceExpression : Direction → ExpHOL 64
  | .up => .op .sub [limitExpression .up, localVar "p"]
  | .down => .op .sub [localVar "p", limitExpression .down]
def outside : Direction → BitVec 64 → BitVec 64 → Prop
  | .up, result, limit => limit < result
  | .down, result, limit => result < limit
def trapCode : Direction → BitVec 64 | .up => 6#64 | .down => 7#64
def trap (direction : Direction) : ProgHOL 64 :=
  .call (some (none, none)) (ofString "trap_with") [.const (trapCode direction)]
def firstGuard (direction : Direction) : ProgHOL 64 :=
  .ite (.cmp .lower (distanceExpression direction) (localVar "n")) (trap direction) .skip
def secondTest : Direction → ExpHOL 64
  | .up => .cmp .lower (limitExpression .up) (localVar "q")
  | .down => .cmp .lower (localVar "q") (limitExpression .down)
def secondGuard (direction : Direction) : ProgHOL 64 := .ite (secondTest direction) (trap direction) .skip
def assignment (direction : Direction) : ProgHOL 64 :=
  .assign .global (ofString (pointerName direction)) (localVar "q")
def returnedExpression : Direction → ExpHOL 64 | .up => localVar "p" | .down => localVar "q"
def resultWord (direction : Direction) (pointer amount : BitVec 64) : BitVec 64 :=
  match direction with | .up => pointer | .down => rounded .down pointer amount

def qTail (direction : Direction) : ProgHOL 64 :=
  .seq (secondGuard direction) (.seq (assignment direction) (.return (returnedExpression direction)))
def pTail (direction : Direction) : ProgHOL 64 :=
  .seq (firstGuard direction) (.dec (ofString "q") .one (roundExpression direction) (qTail direction))
def program (direction : Direction) : ProgHOL 64 :=
  .dec (ofString "p") .one (pointerExpression direction) (pTail direction)
def body : Direction → ProgHOL 64
  | .up => match Guest.guestFn_frame_mem_alloc with | .function fn => progToHOL fn.body | _ => .skip
  | .down => match Guest.guestFn_scratch_alloc with | .function fn => progToHOL fn.body | _ => .skip

theorem body_shape (direction : Direction) : body direction = program direction := by
  cases direction <;>
    simp only [body, Guest.guestFn_frame_mem_alloc, Guest.guestFn_scratch_alloc, progToHOL, expToHOL,
      shapeToHOL, List.map_cons, List.map_nil, Option.map_none, program, pTail, qTail, firstGuard,
      secondGuard, secondTest, trap, trapCode, assignment, pointerExpression, limitExpression,
      distanceExpression, pointerName, limitName, returnedExpression, roundExpression, localVar]

def post {F : Type} (source : PanSemStateFiniteExact 64 F) (direction : Direction) (pointer amount : BitVec 64) :
    PanSemStateFiniteExact 64 F :=
  { source with globals := source.globals.update (ofString (pointerName direction), .val (.word (rounded direction pointer amount))) }

end InitECandidate.Solver.Arenas

#print axioms InitECandidate.Solver.Arenas.body_shape
