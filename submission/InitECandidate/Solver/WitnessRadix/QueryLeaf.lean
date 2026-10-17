import InitECandidate.Solver.WitnessRadix.MemeqEnvironment

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.WitnessRadix.QueryLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

def ordinalExpression : ExpHOL 64 :=
  .shift .lsr (localVar "node") (.const 1#64)
def keysExpression : ExpHOL 64 :=
  .load .one (addConst (localVar "db") 32#64)
def arguments : List (ExpHOL 64) :=
  [.op .add [localVar "keys", .panop .mul [localVar "ordinal", .const 32#64]],
   localVar "hash", .const 32#64]
def equalTest : ExpHOL 64 := .cmp .equal (localVar "equal") (.const 0#64)
def recordExpression : ExpHOL 64 :=
  .load .one (.op .add [.load .one (addConst (localVar "db") 40#64),
    .panop .mul [localVar "ordinal", .const 8#64]])
def returnRecord : ProgHOL 64 :=
  .return (.rstruct [.const 1#64, .load .one (localVar "record"),
    .load .one (addConst (localVar "record") 8#64)])
def afterCompare : ProgHOL 64 :=
  .seq (.ite equalTest QueryEmpty.returnZeros .skip)
    (.dec (ofString "record") .one recordExpression returnRecord)

theorem leaf_shape : leafCode =
    .dec (ofString "ordinal") .one ordinalExpression
      (.dec (ofString "keys") .one keysExpression
        (.decCall (ofString "equal") .one (ofString "memeq") arguments afterCompare)) := by
  simp only [leafCode, QueryEmpty.loopBody, QueryEmpty.body,
    RawProgram.guestFn_nodedb_lookup, progToHOL, expToHOL, shapeToHOL,
    ordinalExpression, keysExpression, arguments, afterCompare, equalTest,
    recordExpression, returnRecord, QueryEmpty.returnZeros, localVar, addConst,
    List.map_cons, List.map_nil]

def found (pointer length : BitVec 64) : ValueHOL 64 :=
  .rStruct [.val (.word 1#64), .val (.word pointer), .val (.word length)]

theorem return_record {F : Type} (source : PanSemStateFiniteExact 64 F)
    (record pointer length : BitVec 64)
    (localRecord : source.locals.lookup (ofString "record") = some (.val (.word record)))
    (mapped : source.memaddrs record) (mappedLength : source.memaddrs (record + 8#64))
    (pointerWord : source.memory record = .word pointer)
    (lengthWord : source.memory (record + 8#64) = .word length) :
    evaluateHOLFiniteState source returnRecord =
      (some (.returned (found pointer length)), emptyLocalsHOLFinite source) := by
  classical
  simp [returnRecord, found, localVar, addConst, evaluateHOLFiniteState_return,
    evalHOLExact, evalListHOLExact, toExact, localRecord, isWfShapeExactHOL,
    memLoadHOLExact, mapped, mappedLength, pointerWord, lengthWord,
    valueIsWord, valueWord, wordOpHOL, wordOp, shapeOfHOLExact, sizeOfShapeWithContextHOL]

theorem after_miss {F : Type} (source : PanSemStateFiniteExact 64 F)
    (unequal : source.locals.lookup (ofString "equal") = some (.val (.word 0#64))) :
    evaluateHOLFiniteState source afterCompare =
      (some (.returned QueryEmpty.zeros), emptyLocalsHOLFinite source) := by
  classical
  rw [afterCompare, evaluateHOLFiniteState_seq, evaluateHOLFiniteState_ite]
  simp [equalTest, localVar, evalHOLExact, toExact, unequal,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL, QueryEmpty.returnZeros,
    QueryEmpty.zeros, evaluateHOLFiniteState_return, evalListHOLExact,
    shapeOfHOLExact, sizeOfShapeWithContextHOL, fixClockHOLFinite, emptyLocalsHOLFinite]

theorem after_hit {F : Type} (source : PanSemStateFiniteExact 64 F)
    (record pointer length : BitVec 64)
    (equal : source.locals.lookup (ofString "equal") = some (.val (.word 1#64)))
    (readRecord : eval source recordExpression = some (.val (.word record)))
    (mapped : source.memaddrs record) (mappedLength : source.memaddrs (record + 8#64))
    (pointerWord : source.memory record = .word pointer)
    (lengthWord : source.memory (record + 8#64) = .word length) :
    evaluateHOLFiniteState source afterCompare =
      (some (.returned (found pointer length)),
        restore source "record" (emptyLocalsHOLFinite (bind source "record" record))) := by
  classical
  have skipped : evaluateHOLFiniteState source (.ite equalTest QueryEmpty.returnZeros .skip) =
      (none, source) := by
    rw [evaluateHOLFiniteState_ite]
    simp [equalTest, localVar, evalHOLExact, toExact, equal,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have localRecord : (bind source "record" record).locals.lookup (ofString "record") =
      some (.val (.word record)) := by
    simp [QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have returned := return_record (bind source "record" record) record pointer length
    localRecord mapped mappedLength pointerWord lengthWord
  rw [afterCompare, evaluateHOLFiniteState_seq, skipped]
  have fixed : fixClockHOLFinite source ((none : Option (PanSemResultExact 64)), source) =
      (none, source) := by simp [fixClockHOLFinite]
  simp only [fixed]
  rw [evaluateHOLFiniteState_dec_total]
  simp only [eval] at readRecord
  simp only [readRecord, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
  change (let output := evaluateHOLFiniteState (bind source "record" record) returnRecord;
    (output.1, restore source "record" output.2)) = _
  rw [returned]

end InitECandidate.Solver.WitnessRadix.QueryLeaf

#print axioms InitECandidate.Solver.WitnessRadix.QueryLeaf.leaf_shape
#print axioms InitECandidate.Solver.WitnessRadix.QueryLeaf.after_miss
#print axioms InitECandidate.Solver.WitnessRadix.QueryLeaf.after_hit
