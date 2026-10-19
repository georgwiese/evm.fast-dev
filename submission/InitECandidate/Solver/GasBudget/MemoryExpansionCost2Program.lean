import InitECandidate.Solver.GasBudget.MemoryExpansionCostPrefix
import InitECandidate.Solver.Input.NormalWordDeclaration
import InitECandidate.Solver.WitnessRadix.StoreWord

namespace InitECandidate.Solver.GasBudget.MemoryExpansionCost2
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Input.RlpWrite

def body : ProgHOL 64 := match Guest.guestFn_extend_memory_cost2 with | .function fn => progToHOL fn.body | _ => .skip
def pairShape : ShapeHOL := .comb [.one, .one]
def part (name : String) (index : Nat) : ExpHOL 64 := .rfield index (localVar name)
def maxGuard (name : String) : ProgHOL 64 := .ite (.cmp .equal (part name 0) (.const 18446744073709551615#64))
  (.return (localVar name)) .skip
def finish : ProgHOL 64 := .return (.rstruct [.op .add [part "a" 0, part "b" 0], .op .add [part "a" 1, part "b" 1]])
def afterB : ProgHOL 64 := .seq (.store (frameAddress 32#64) (localVar "saved")) (.seq (maxGuard "b") finish)
def afterTemporary : ProgHOL 64 := .decCall (ofString "b") pairShape (ofString "extend_memory_cost1") [localVar "s2", localVar "n2"] afterB
def temporaryValue : ExpHOL 64 := .op .add [localVar "saved", part "a" 1]
def afterSaved : ProgHOL 64 := .seq (.store (frameAddress 32#64) temporaryValue) afterTemporary
def afterA : ProgHOL 64 := .seq (maxGuard "a") (.dec (ofString "saved") .one (frameLoad 32#64) afterSaved)

theorem body_shape : body = .decCall (ofString "a") pairShape (ofString "extend_memory_cost1") [localVar "s1", localVar "n1"] afterA := by
  simp only [body, Guest.guestFn_extend_memory_cost2, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    Option.map_none, pairShape, part, afterA, maxGuard, afterSaved, afterTemporary, afterB, finish, temporaryValue, localVar, frameLoad, frameAddress]

def merge (a b : BitVec 64 × BitVec 64) : BitVec 64 × BitVec 64 :=
  if b.1 = 18446744073709551615#64 then b else (a.1 + b.1, a.2 + b.2)
def resultPair (s1 n1 s2 n2 : U256Value.Words) (current : BitVec 64) : BitVec 64 × BitVec 64 :=
  let a := MemoryExpansionCost.resultPair s1 n1 current
  if a.1 = 18446744073709551615#64 then a else merge a (MemoryExpansionCost.resultPair s2 n2 (current + a.2))

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) : code.lookup (ofString "extend_memory_cost2") = some
    ([(ofString "s1", U256Value.tupleShape), (ofString "n1", U256Value.tupleShape), (ofString "s2", U256Value.tupleShape), (ofString "n2", U256Value.tupleShape)], body, pairShape) := by
  have checked := Input.OriginalCode.indexed code installed 417 (OriginalCodeEnvironment.originalEntry Guest.guestFn_extend_memory_cost2) (by rfl)
  simpa only [OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, Guest.guestFn_extend_memory_cost2,
    body, pairShape, U256Value.tupleShape, paramToHOL, shapeToHOL, List.map_cons, List.map_nil] using checked

theorem restore_memory (memory : WitnessRadix.WordWrites.Memory) (address old temporary : BitVec 64)
    (cell : memory address = .word old) : WitnessRadix.StoreWord.put (WitnessRadix.StoreWord.put memory address temporary) address old = memory := by
  funext query
  by_cases equal : query = address
  · subst query; simp [WitnessRadix.StoreWord.put, cell]
  · simp [WitnessRadix.StoreWord.put, equal]

end InitECandidate.Solver.GasBudget.MemoryExpansionCost2

#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost2.body_shape
#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost2.original_code
#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost2.restore_memory
