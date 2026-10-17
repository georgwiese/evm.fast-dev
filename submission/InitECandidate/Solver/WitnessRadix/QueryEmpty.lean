import InitECandidate.Solver.WitnessRadix.RawProgram
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-! A first execution connection for the actual proposed lookup AST. The
empty-root case neither calls memeq nor reads any key or table backing array.
The generic nonempty case is a separate graph/memory invariant obligation. -/
namespace InitECandidate.Solver.WitnessRadix.QueryEmpty
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open PanSemStateFiniteExact

def body : ProgHOL 64 :=
  match RawProgram.guestFn_nodedb_lookup with
  | .function fn => progToHOL fn.body
  | _ => .skip

def rootExpression : ExpHOL 64 :=
  .load .one (.op .add [.var .local (ofString "db"), .const 24#64])

def condition : ExpHOL 64 :=
  .cmp .notEqual (.var .local (ofString "node")) (.const 0#64)

def loopBody : ProgHOL 64 :=
  match body with
  | .dec _ _ _ (.seq (.while _ loop) _) => loop
  | _ => .skip

def returnZeros : ProgHOL 64 :=
  .return (.rstruct [.const 0#64, .const 0#64, .const 0#64])

theorem body_shape : body =
    .dec (ofString "node") .one rootExpression (.seq (.while condition loopBody) returnZeros) := by
  simp only [loopBody, body, RawProgram.guestFn_nodedb_lookup, progToHOL,
    expToHOL, shapeToHOL, rootExpression, condition, returnZeros, List.map_cons, List.map_nil]

def zeros : ValueHOL 64 := .rStruct [.val (.word 0), .val (.word 0), .val (.word 0)]

noncomputable def readRoot {F : Type} (source : PanSemStateFiniteExact 64 F) :
    Option (ValueHOL 64) :=
  @evalHOLFinite 64 F _ source (fun address => Classical.propDecidable (source.memaddrs address))
    rootExpression

theorem readRoot_of_cell {F : Type} (source : PanSemStateFiniteExact 64 F) (table : BitVec 64)
    (argument : source.locals.lookup (ofString "db") = some (.val (.word table)))
    (mapped : source.memaddrs (table + 24#64))
    (root : source.memory (table + 24#64) = .word 0) :
    readRoot source = some (.val (.word 0)) := by
  classical
  simp [readRoot, rootExpression, evalHOLFinite, evalHOLExact, evalListHOLExact, toExact,
    argument, isWfShapeExactHOL, valueIsWord, valueWord, wordOpHOL, wordOp,
    memLoadHOLExact, mapped, root]

/-- The actual lookup function returns the absent triple on an empty root,
for every source clock. All data-array and key loads are unreachable. -/
theorem empty_root {F : Type} (source : PanSemStateFiniteExact 64 F)
    (empty : readRoot source = some (.val (.word 0))) :
    (evaluateHOLFiniteState source body).1 = some (.returned zeros) ∧
    (evaluateHOLFiniteState source body).2.memory = source.memory ∧
    (evaluateHOLFiniteState source body).2.ffi = source.ffi ∧
    (evaluateHOLFiniteState source body).2.clock = source.clock := by
  classical
  let loaded := setVarHOLFinite (ofString "node") (.val (.word 0)) source
  have test : @evalHOLFinite 64 F _ loaded
      (fun address => Classical.propDecidable (loaded.memaddrs address)) condition =
      some (.val (.word 0)) := by
    simp [loaded, condition, evalHOLFinite, evalHOLExact, setVarHOLFinite,
      toExact, HolFiniteMapExact.update, FUPDATE, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have stopped : evaluateHOLFiniteState loaded (.while condition loopBody) = (none, loaded) := by
    rw [evaluateHOLFiniteState_while_total, test]
    simp
  have returned : evaluateHOLFiniteState loaded returnZeros =
      (some (.returned zeros), emptyLocalsHOLFinite loaded) := by
    simp [returnZeros, zeros, evaluateHOLFiniteState_return, evalHOLExact, evalListHOLExact,
      shapeOfHOLExact, sizeOfShapeWithContextHOL]
  have sequence : evaluateHOLFiniteState loaded (.seq (.while condition loopBody) returnZeros) =
      (some (.returned zeros), emptyLocalsHOLFinite loaded) := by
    rw [evaluateHOLFiniteState_seq, stopped]
    have fixed : fixClockHOLFinite loaded ((none : Option (PanSemResultExact 64)), loaded) =
        (none, loaded) := by
      simp [fixClockHOLFinite]
    simpa only [fixed] using returned
  simp only [readRoot, evalHOLFinite] at empty
  have entire : evaluateHOLFiniteState source body =
      (some (.returned zeros), { emptyLocalsHOLFinite loaded with
        locals := HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite loaded).locals
          (ofString "node", source.locals.lookup (ofString "node")) }) := by
    rw [body_shape, evaluateHOLFiniteState_dec_total]
    simp only [empty, shapeEqHOL, shapeOfHOLExact, ↓reduceIte]
    change (let output := evaluateHOLFiniteState loaded (.seq (.while condition loopBody) returnZeros)
            (output.1, { output.2 with
              locals := HolFiniteMapExact.resVarEq output.2.locals
                (ofString "node", source.locals.lookup (ofString "node")) })) = _
    rw [sequence]
  rw [entire]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem empty_table {F : Type} (source : PanSemStateFiniteExact 64 F) (table : BitVec 64)
    (argument : source.locals.lookup (ofString "db") = some (.val (.word table)))
    (mapped : source.memaddrs (table + 24#64))
    (root : source.memory (table + 24#64) = .word 0) :
    (evaluateHOLFiniteState source body).1 = some (.returned zeros) ∧
    (evaluateHOLFiniteState source body).2.memory = source.memory ∧
    (evaluateHOLFiniteState source body).2.ffi = source.ffi ∧
    (evaluateHOLFiniteState source body).2.clock = source.clock :=
  empty_root source (readRoot_of_cell source table argument mapped root)

end InitECandidate.Solver.WitnessRadix.QueryEmpty

#print axioms InitECandidate.Solver.WitnessRadix.QueryEmpty.empty_root
#print axioms InitECandidate.Solver.WitnessRadix.QueryEmpty.empty_table
