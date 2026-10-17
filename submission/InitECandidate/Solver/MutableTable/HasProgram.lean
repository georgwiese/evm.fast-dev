import InitECandidate.Solver.MutableTable.FindCall32

namespace InitECandidate.Solver.MutableTable.Has
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_htab_has with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := Find.formals
def condition : ExpHOL 64 := .cmp .equal (localVar "i") (Find.tableLoad 16#64)
def absent : ProgHOL 64 := .return (.const 0#64)
def present : ProgHOL 64 := .return (.const 1#64)
def afterIndex : ProgHOL 64 := .seq (.ite condition absent .skip) present

theorem body_shape : body = .decCall (ofString "i") .one (ofString "htab_find_slot") [localVar "t", localVar "key"] afterIndex := by
  simp only [body, Guest.guestFn_htab_has, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    afterIndex, condition, absent, present, Find.tableLoad, localVar]

theorem tail_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table index capacity : BitVec 64)
    (tLocal : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (iLocal : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (mapped : source.memaddrs (table + 16#64)) (cell : source.memory (table + 16#64) = .word capacity) :
    evaluateHOLFiniteState source afterIndex =
      (some (.returned (.val (.word (if index = capacity then 0#64 else 1#64)))), emptyLocalsHOLFinite source) := by
  have capRead := Find.table_read source table 16#64 capacity tLocal mapped cell
  simp only [eval] at capRead
  by_cases same : index = capacity
  · have stopped : evaluateHOLFiniteState source (.ite condition absent .skip) =
        (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite source) := by
      simp [condition, evaluateHOLFiniteState_ite, evalHOLExact, toExact, localVar, iLocal, capRead, same,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, absent, evaluateHOLFiniteState_return, shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [afterIndex, WitnessRadix.StateSteps.stopped_sequence source (emptyLocalsHOLFinite source) _ _ _ stopped (Nat.le_refl _)]
    simp only [same, ↓reduceIte]
  · have skipped : evaluateHOLFiniteState source (.ite condition absent .skip) = (none, source) := by
      simp [condition, evaluateHOLFiniteState_ite, evalHOLExact, toExact, localVar, iLocal, capRead, same,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    rw [afterIndex, WitnessRadix.StateSteps.next_sequence source source _ _ skipped (Nat.le_refl _)]
    simp [present, evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL, same]

end InitECandidate.Solver.MutableTable.Has

#print axioms InitECandidate.Solver.MutableTable.Has.body_shape
#print axioms InitECandidate.Solver.MutableTable.Has.tail_execute
