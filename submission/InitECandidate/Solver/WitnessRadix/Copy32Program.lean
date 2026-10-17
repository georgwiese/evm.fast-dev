import InitECandidate.Solver.PanTraversal
import InitECandidate.Solver.WitnessRadix.WordWrites
import Guest.Ast

namespace InitECandidate.Solver.WitnessRadix.Copy32
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_memcpy with | .function fn => progToHOL fn.body | _ => .skip

def loop32 : ProgHOL 64 := (BuildProgram.loops body)[0]?.getD .skip
def loopWord : ProgHOL 64 := (BuildProgram.loops body)[1]?.getD .skip
def loopBytes : ProgHOL 64 := (BuildProgram.loops body)[2]?.getD .skip
def loopTail : ProgHOL 64 := (BuildProgram.loops body)[3]?.getD .skip

def condition (step : BitVec 64) : ExpHOL 64 := .cmp .notLower (localVar "n") (addConst (localVar "i") step)
def alignment : ExpHOL 64 := .cmp .equal (.op .and [.op .or [localVar "dst", localVar "src"], .const 7#64]) (.const 0#64)
def address (name : String) (offset : Nat) : ExpHOL 64 :=
  if offset = 0 then .op .add [localVar name, localVar "i"]
  else .op .add [localVar name, localVar "i", .const (BitVec.ofNat 64 offset)]
def wordStore (offset : Nat) : ProgHOL 64 := .store (address "dst" offset) (.load .one (address "src" offset))
def wordBody : ProgHOL 64 := .seq (wordStore 0) (.seq (wordStore 8) (.seq (wordStore 16) (.seq (wordStore 24)
  (.assign .local (ofString "i") (addConst (localVar "i") 32#64)))))

theorem loop32_shape : loop32 = .while (condition 32#64) wordBody := by
  simp only [loop32, body, BuildProgram.loops, Guest.guestFn_memcpy, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, List.nil_append, List.cons_append, List.append_nil,
    List.getElem?_cons_zero, Option.getD_some, condition, wordBody, wordStore, address,
    localVar, addConst, ↓reduceIte]
  rfl

theorem body_shape : body = .dec (ofString "i") .one (.const 0#64)
    (.seq (.ite alignment (.seq loop32 loopWord) .skip)
      (.seq loopBytes (.seq loopTail (.return (.const 0#64))))) := by
  simp only [body, alignment, loop32, loopWord, loopBytes, loopTail, BuildProgram.loops, Guest.guestFn_memcpy,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, List.nil_append, List.cons_append,
    List.append_nil, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, localVar]

def writes (dst : BitVec 64) (words : Fin 4 → BitVec 64) : List (BitVec 64 × BitVec 64) :=
  [(dst, words 0), (dst + 8#64, words 1), (dst + 16#64, words 2), (dst + 24#64, words 3)]

def memory (source : WordWrites.Memory) (dst : BitVec 64) (words : Fin 4 → BitVec 64) : WordWrites.Memory :=
  WordWrites.write source (writes dst words)

end InitECandidate.Solver.WitnessRadix.Copy32

#print axioms InitECandidate.Solver.WitnessRadix.Copy32.loop32_shape
#print axioms InitECandidate.Solver.WitnessRadix.Copy32.body_shape
