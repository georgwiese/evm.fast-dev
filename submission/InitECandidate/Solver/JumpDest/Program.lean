import InitECandidate.Solver.Arenas.Calls
import InitECandidate.Solver.WitnessRadix.ZeroCall

namespace InitECandidate.Solver.JumpDest
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def truth (expression : ExpHOL 64) : ExpHOL 64 := .cmp .notEqual (.const 0#64) expression

def inRange (name : String) (low high : BitVec 64) : ExpHOL 64 :=
  .op .and [truth (.cmp .notLower (localVar name) (.const low)),
    truth (.cmp .notLower (.const high) (localVar name))]
def bytesExpression : ExpHOL 64 := .op .add [
  .panop .mul [.shift .lsr (.op .add [localVar "n", .const 63#64]) (.const 6#64), .const 8#64], .const 8#64]
def bitmapAddress : ExpHOL 64 := .op .add [localVar "bm",
  .panop .mul [.shift .lsr (localVar "pc") (.const 6#64), .const 8#64]]
def bitmapValue : ExpHOL 64 := .op .or [.load .one bitmapAddress,
  .shift .lsl (.const 1#64) (.op .and [localVar "pc", .const 63#64])]
def mark : ProgHOL 64 := .store bitmapAddress bitmapValue

def setAdvance (word : BitVec 64) : ProgHOL 64 := .assign .local (ofString "adv") (.const word)
def hasNext : ExpHOL 64 := .cmp .lower (.op .add [localVar "pc", .const 1#64]) (localVar "n")
def nextByte : ExpHOL 64 := .loadByte (.op .add [localVar "code", localVar "pc", .const 1#64])
def continuationAdvance (name : String) (low : BitVec 64) : ProgHOL 64 :=
  .seq (setAdvance 2#64)
    (.ite hasNext (.dec (ofString name) .one nextByte (.ite (inRange name low 127#64) (setAdvance 1#64) .skip)) .skip)
def pushTest : ExpHOL 64 := inRange "op" 96#64 127#64
def pushAdvance : ProgHOL 64 := .assign .local (ofString "adv")
  (.op .add [.op .sub [localVar "op", .const 96#64], .const 2#64])
def wideTest : ExpHOL 64 := truth (.op .or [
  .cmp .equal (localVar "op") (.const 230#64), .cmp .equal (localVar "op") (.const 231#64)])
def branch : ProgHOL 64 :=
  .ite (.cmp .equal (localVar "op") (.const 91#64)) mark
    (.ite pushTest pushAdvance
      (.seq (.ite wideTest (continuationAdvance "nx" 91#64) .skip)
        (.ite (.cmp .equal (localVar "op") (.const 232#64)) (continuationAdvance "nx2" 82#64) .skip)))
def advancePC : ProgHOL 64 := .assign .local (ofString "pc") (.op .add [localVar "pc", localVar "adv"])
def step : ProgHOL 64 :=
  .dec (ofString "op") .one (.loadByte (.op .add [localVar "code", localVar "pc"]))
    (.dec (ofString "adv") .one (.const 1#64) (.seq branch advancePC))
def condition : ExpHOL 64 := .cmp .lower (localVar "pc") (localVar "n")
def loop : ProgHOL 64 := .while condition step
def afterClear : ProgHOL 64 := .dec (ofString "pc") .one (.const 0#64)
  (.seq loop (.return (localVar "bm")))
def clear : ProgHOL 64 := .call (some (none, none)) (ofString "memzero") [localVar "bm", bytesExpression]
def program : ProgHOL 64 := .decCall (ofString "bm") .one (ofString "scratch_alloc") [bytesExpression]
  (.seq clear afterClear)
def body : ProgHOL 64 := match Guest.guestFn_compute_jumpdests with | .function fn => progToHOL fn.body | _ => .skip

theorem body_shape : body = program := by
  simp only [body, Guest.guestFn_compute_jumpdests, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, Option.map_some, program, clear, afterClear,
    loop, condition, step, branch, mark, bitmapAddress, bitmapValue, pushTest, pushAdvance,
    wideTest, continuationAdvance, inRange, truth, hasNext, nextByte, setAdvance, advancePC,
    bytesExpression, localVar]

end InitECandidate.Solver.JumpDest

#print axioms InitECandidate.Solver.JumpDest.body_shape
