import InitECandidate.Solver.WitnessRadix.QueryEmpty
import InitECandidate.Solver.WitnessRadix.WordBits

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.WitnessRadix.QueryBranch
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open PanSemStateFiniteExact

def localVar (name : String) : ExpHOL 64 := .var .local (ofString name)
def addConst (expression : ExpHOL 64) (offset : BitVec 64) : ExpHOL 64 :=
  .op .add [expression, .const offset]
def leafTest : ExpHOL 64 :=
  .cmp .notEqual (.op .and [localVar "node", .const 1#64]) (.const 0#64)
def bitLoad : ExpHOL 64 := .load .one (localVar "node")
def digitExpression : ExpHOL 64 :=
  .op .and [
    .shift .lsr
      (.loadByte (.op .add [localVar "hash", .shift .lsr (localVar "bit") (.const 3#64)]))
      (.op .and [localVar "bit", .const 7#64]), .const 1#64]
def digitTest : ExpHOL 64 := .cmp .equal (localVar "digit") (.const 0#64)
def assignChild (offset : BitVec 64) : ProgHOL 64 :=
  .assign .local (ofString "node") (.load .one (addConst (localVar "node") offset))
def branchCode : ProgHOL 64 :=
  .dec (ofString "bit") .one bitLoad
    (.dec (ofString "digit") .one digitExpression
      (.ite digitTest (assignChild 8#64) (assignChild 16#64)))
def leafCode : ProgHOL 64 :=
  match QueryEmpty.loopBody with
  | .seq (.ite _ leaf _) _ => leaf
  | _ => .skip

theorem loop_shape : QueryEmpty.loopBody =
    .seq (.ite leafTest leafCode .skip) branchCode := by
  simp only [QueryEmpty.loopBody, QueryEmpty.body, RawProgram.guestFn_nodedb_lookup,
    leafTest, leafCode, branchCode, bitLoad, digitExpression, digitTest, assignChild,
    addConst, localVar, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil]

noncomputable def eval {F : Type} (state : PanSemStateFiniteExact 64 F)
    (expression : ExpHOL 64) : Option (ValueHOL 64) :=
  @evalHOLExact 64 F _ state.toExact
    (fun address => Classical.propDecidable (state.memaddrs address)) expression

private theorem andOnes (word : BitVec 64) :
    AndOp.and word (18446744073709551615#64) = word := by
  change word &&& BitVec.allOnes 64 = word
  exact BitVec.and_allOnes

private theorem opAnd (left right : BitVec 64) :
    wordOpHOL .and [left, right] = some (left &&& right) := by
  change some (AndOp.and left (AndOp.and right (18446744073709551615#64))) = _
  rw [andOnes]
  rfl

private theorem opAdd (left right : BitVec 64) :
    wordOpHOL .add [left, right] = some (left + right) := by
  simp [wordOpHOL, wordOp]

theorem eval_leafTest {F : Type} (state : PanSemStateFiniteExact 64 F) (root : BitVec 64)
    (node : state.locals.lookup (ofString "node") = some (.val (.word root)))
    (even : root &&& 1#64 = 0#64) : eval state leafTest = some (.val (.word 0#64)) := by
  classical
  simp [eval, leafTest, localVar, evalHOLExact, evalListHOLExact, toExact, node,
    valueIsWord, valueWord, wordOpHOL, wordOp, andOnes, even,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  exact even

theorem eval_bitLoad {F : Type} (state : PanSemStateFiniteExact 64 F) (root position : BitVec 64)
    (node : state.locals.lookup (ofString "node") = some (.val (.word root)))
    (mapped : state.memaddrs root) (word : state.memory root = .word position) :
    eval state bitLoad = some (.val (.word position)) := by
  classical
  simp [eval, bitLoad, localVar, evalHOLExact, toExact, node,
    isWfShapeExactHOL, memLoadHOLExact, mapped, word]

theorem eval_digit {F : Type} (state : PanSemStateFiniteExact 64 F)
    (query position : BitVec 64) (byte : UInt8)
    (hash : state.locals.lookup (ofString "hash") = some (.val (.word query)))
    (bit : state.locals.lookup (ofString "bit") = some (.val (.word position)))
    (loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be
      (query + (position >>> (3 : Nat))) = some byte) :
    eval state digitExpression =
      some (.val (.word (WordBits.digit (BitVec.ofNat 8 byte.toNat) position))) := by
  classical
  have shiftSmall : ¬ ((position &&& 7#64).toNat ≠ 0 ∧ 64 ≤ (position &&& 7#64).toNat) := by
    rw [WordBits.mask7]
    omega
  have widened : BitVec.ofNat 64 byte.toNat = (BitVec.ofNat 8 byte.toNat).setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
    have small : byte.toNat < 256 := byte.toNat_lt_size
    simp [Nat.mod_eq_of_lt (show byte.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt small]
  have threeNat : (3#64).toNat = 3 := rfl
  have threeFits : ¬ (3 ≠ 0 ∧ 64 ≤ (3 : Nat)) := by decide
  simp only [eval, digitExpression, localVar, evalHOLExact, evalListHOLExact, toExact,
    hash, bit, valueIsWord, valueWord, List.all_cons, List.all_nil, Bool.and_self,
    Bool.and_true, List.map_cons, List.map_nil, opAnd, opAdd, Option.map_some,
    ↓reduceIte, wordShiftHOL, threeNat, threeFits, shiftSmall, loaded]
  rw [widened]
  rfl

theorem eval_child {F : Type} (state : PanSemStateFiniteExact 64 F)
    (root offset child : BitVec 64)
    (node : state.locals.lookup (ofString "node") = some (.val (.word root)))
    (mapped : state.memaddrs (root + offset)) (word : state.memory (root + offset) = .word child) :
    eval state (.load .one (addConst (localVar "node") offset)) =
      some (.val (.word child)) := by
  classical
  simp [eval, addConst, localVar, evalHOLExact, evalListHOLExact, toExact, node,
    isWfShapeExactHOL, memLoadHOLExact, mapped, word, valueIsWord, valueWord, wordOpHOL, wordOp]

theorem assign_child {F : Type} (state : PanSemStateFiniteExact 64 F)
    (root offset child : BitVec 64)
    (node : state.locals.lookup (ofString "node") = some (.val (.word root)))
    (mapped : state.memaddrs (root + offset)) (word : state.memory (root + offset) = .word child) :
    evaluateHOLFiniteState state (assignChild offset) =
      (none, setVarHOLFinite (ofString "node") (.val (.word child)) state) := by
  classical
  have load := eval_child state root offset child node mapped word
  have valid : isValidValueHOLFinite state .local (ofString "node") (.val (.word child)) = true := by
    simp [isValidValueHOLFinite, lookupKvarHOLFinite, node, shapeOfHOLExact, shapeEqHOL]
  rw [assignChild, evaluateHOLFiniteState_assign]
  simp only [eval] at load
  rw [load]
  simp only [← isValidValueHOLFinite_eq, valid, ↓reduceIte, setKvarHOLFinite]

end InitECandidate.Solver.WitnessRadix.QueryBranch

#print axioms InitECandidate.Solver.WitnessRadix.QueryBranch.loop_shape
#print axioms InitECandidate.Solver.WitnessRadix.QueryBranch.eval_digit
#print axioms InitECandidate.Solver.WitnessRadix.QueryBranch.assign_child
