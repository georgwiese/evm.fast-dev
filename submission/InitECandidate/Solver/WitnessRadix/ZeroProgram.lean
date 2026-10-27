import InitECandidate.Solver.WitnessRadix.Copy32Program
import Guest.SoftwareAst

namespace InitECandidate.Solver.WitnessRadix.Zero
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString QueryBranch

def body : ProgHOL 64 := match Guest.Software.guestFn_memzero with
  | .function fn => progToHOL fn.body | _ => .skip
def loop32 : ProgHOL 64 := (BuildProgram.loops body)[0]?.getD .skip
def loopWord : ProgHOL 64 := (BuildProgram.loops body)[1]?.getD .skip
def loopBytes : ProgHOL 64 := (BuildProgram.loops body)[2]?.getD .skip
def loopTail : ProgHOL 64 := (BuildProgram.loops body)[3]?.getD .skip
def alignment : ExpHOL 64 := .cmp .equal (.op .and [localVar "dst", .const 7#64]) (.const 0#64)
def condition (step : BitVec 64) : ExpHOL 64 := Copy32.condition step
def increment (step : BitVec 64) : ProgHOL 64 := .assign .local (ofString "i") (addConst (localVar "i") step)
def wordStore (offset : Nat) : ProgHOL 64 := .store (Copy32.address "dst" offset) (.const 0#64)
def block32 : ProgHOL 64 := .seq (wordStore 0) (.seq (wordStore 8) (.seq (wordStore 16)
  (.seq (wordStore 24) (increment 32#64))))
def blockWord : ProgHOL 64 := .seq (wordStore 0) (increment 8#64)

theorem loop32_shape : loop32 = .while (condition 32#64) block32 := by
  simp only [loop32, body, BuildProgram.loops, Guest.Software.guestFn_memzero, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, List.nil_append, List.cons_append, List.append_nil,
    List.getElem?_cons_zero, Option.getD_some, condition, Copy32.condition,
    block32, wordStore, Copy32.address, increment, localVar, addConst, ↓reduceIte]
  rfl

theorem loopWord_shape : loopWord = .while (condition 8#64) blockWord := by
  simp only [loopWord, body, BuildProgram.loops, Guest.Software.guestFn_memzero, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, List.nil_append, List.cons_append, List.append_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, condition, Copy32.condition,
    blockWord, wordStore, Copy32.address, increment, localVar, addConst, ↓reduceIte]

theorem body_shape : body = .dec (ofString "i") .one (.const 0#64)
    (.seq (.ite alignment (.seq loop32 loopWord) .skip)
      (.seq loopBytes (.seq loopTail (.return (.const 0#64))))) := by
  simp only [body, alignment, loop32, loopWord, loopBytes, loopTail, BuildProgram.loops, Guest.Software.guestFn_memzero,
    progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, List.nil_append, List.cons_append,
    List.append_nil, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, localVar]

end InitECandidate.Solver.WitnessRadix.Zero

#print axioms InitECandidate.Solver.WitnessRadix.Zero.loop32_shape
#print axioms InitECandidate.Solver.WitnessRadix.Zero.loopWord_shape
#print axioms InitECandidate.Solver.WitnessRadix.Zero.body_shape
