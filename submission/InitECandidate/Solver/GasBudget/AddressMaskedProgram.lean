import InitECandidate.Solver.GasBudget.Be64Normal
import InitECandidate.Solver.Input.NormalWordDeclaration

namespace InitECandidate.Solver.GasBudget.AddressMasked
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Input.RlpWrite MemoryWriter

def body : ProgHOL 64 := match Guest.guestFn_to_address_masked with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "v", U256Value.tupleShape)]
def address (offset : Nat) : ExpHOL 64 := if offset = 0 then localVar "a" else .op .add [localVar "a", .const (BitVec.ofNat 64 offset)]
def arguments (offset : Nat) (index : Fin 4) : List (ExpHOL 64) := [address offset, .rfield index.val (localVar "v")]
def third : ProgHOL 64 := .seq (.call (some (none, none)) (ofString "st_be64") (arguments 12 0)) (.return (localVar "a"))
def second : ProgHOL 64 := .seq (.call (some (none, none)) (ofString "st_be64") (arguments 4 1)) third
def stores : ProgHOL 64 := .seq (.call (some (none, none)) (ofString "st_be32") (arguments 0 2)) second
def pointerExpression : ExpHOL 64 := .op .add [.var .global (ofString "ev"), .const 240#64]

theorem body_shape : body = .dec (ofString "a") .one pointerExpression stores := by
  simp only [body, Guest.guestFn_to_address_masked, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    pointerExpression, stores, second, third, arguments, address, localVar, Option.map_none, ↓reduceIte]
  rfl

theorem arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (words : U256Value.Words) (offset : Nat) (index : Fin 4)
    (pointerLocal : source.locals.lookup (ofString "a") = some (.val (.word pointer)))
    (valueLocal : source.locals.lookup (ofString "v") = some (U256Value.tuple words)) :
    evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) (arguments offset index) =
      some [.val (.word (pointer + BitVec.ofNat 64 offset)), .val (.word (words index))] := by
  have choices : index.val = 0 ∨ index.val = 1 ∨ index.val = 2 ∨ index.val = 3 := by have bound := index.isLt; omega
  obtain ⟨index, bound⟩ := index
  rcases choices with rfl | rfl | rfl | rfl
  all_goals by_cases zero : offset = 0
  all_goals simp [arguments, address, zero, evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar,
    pointerLocal, valueLocal, U256Value.tuple, valueIsWord, valueWord, wordOpHOL, wordOp]

end InitECandidate.Solver.GasBudget.AddressMasked

#print axioms InitECandidate.Solver.GasBudget.AddressMasked.body_shape
#print axioms InitECandidate.Solver.GasBudget.AddressMasked.arguments_read
