import InitECandidate.Solver.WitnessRadix.QueryExecution

namespace InitECandidate.Solver.WitnessRadix.QueryExecution
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch QueryLeaf

noncomputable local instance : DecidableEq ByteKeys.Key := Classical.decEq _

def tailCode : ProgHOL 64 := .seq QueryLoop.loop QueryEmpty.returnZeros

theorem zeros_return {F : Type} (source : PanSemStateFiniteExact 64 F) :
    evaluateHOLFiniteState source QueryEmpty.returnZeros =
      (some (.returned QueryEmpty.zeros), emptyLocalsHOLFinite source) := by
  classical
  simp [QueryEmpty.returnZeros, QueryEmpty.zeros, evaluateHOLFiniteState_return,
    evalHOLExact, evalListHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]

theorem finish_loop {F : Type} (source : PanSemStateFiniteExact 64 F)
    (answer : Option Graph.Slice) (paid : Nat)
    (correct : Correct (evaluateHOLFiniteState source QueryLoop.loop).1 answer)
    (frame : emptyLocalsHOLFinite (evaluateHOLFiniteState source QueryLoop.loop).2 =
      emptyLocalsHOLFinite { source with clock := source.clock - paid }) :
    (evaluateHOLFiniteState source tailCode).1 = some (.returned (valueOf answer)) ∧
    emptyLocalsHOLFinite (evaluateHOLFiniteState source tailCode).2 =
      emptyLocalsHOLFinite { source with clock := source.clock - paid } := by
  classical
  have clockEq := congrArg (fun state : PanSemStateFiniteExact 64 F => state.clock) frame
  change (evaluateHOLFiniteState source QueryLoop.loop).2.clock = source.clock - paid at clockEq
  have notGreater : ¬ source.clock < (evaluateHOLFiniteState source QueryLoop.loop).2.clock := by omega
  have fixed : fixClockHOLFinite source (evaluateHOLFiniteState source QueryLoop.loop) =
      evaluateHOLFiniteState source QueryLoop.loop := by
    simp only [fixClockHOLFinite, notGreater, ↓reduceIte]
  rw [tailCode, evaluateHOLFiniteState_seq]
  simp only [fixed]
  rcases correct with returned | ⟨absent, noAnswer⟩
  · simp only [returned]
    exact ⟨True.intro, frame⟩
  · simp only [absent]
    rw [zeros_return, noAnswer]
    exact ⟨rfl, by simpa only [emptyLocalsHOLFinite] using frame⟩

theorem read_root {F : Type} (source : PanSemStateFiniteExact 64 F) (table root : BitVec 64)
    (db : source.locals.lookup (ofString "db") = some (.val (.word table)))
    (mapped : source.memaddrs (table + 24#64))
    (stored : source.memory (table + 24#64) = .word root) :
    eval source QueryEmpty.rootExpression = some (.val (.word root)) := by
  classical
  simp [eval, QueryEmpty.rootExpression, evalHOLExact, evalListHOLExact, toExact,
    db, isWfShapeExactHOL, valueIsWord, valueWord, wordOpHOL, wordOp,
    memLoadHOLExact, mapped, stored]

/-- The complete literal candidate lookup body, from concrete header cells,
an immutable tree representation and the original fixed memeq code entry. -/
theorem lookup_tree {F : Type} (tree : Graph.Tree) (source : PanSemStateFiniteExact 64 F)
    (table keys vals hash root : BitVec 64) (query : ByteKeys.Key)
    (rep : QueryMemory.Represents source table keys vals root tree)
    (rootMapped : source.memaddrs (table + 24#64))
    (rootWord : source.memory (table + 24#64) = .word root)
    (db : source.locals.lookup (ofString "db") = some (.val (.word table)))
    (hashLocal : source.locals.lookup (ofString "hash") = some (.val (.word hash)))
    (code : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (view : MemoryBytes.ByteView source hash query)
    (fits : hash.toNat + 32 < 2 ^ 64) (little : source.be = false)
    (enough : compactHeight tree + 6 ≤ source.clock) :
    ∃ paid, paid ≤ compactHeight tree + 6 ∧
      (evaluateHOLFiniteState source QueryEmpty.body).1 =
        some (.returned (valueOf (fastLookup ByteKeys.bit query tree))) ∧
      emptyLocalsHOLFinite (evaluateHOLFiniteState source QueryEmpty.body).2 =
        emptyLocalsHOLFinite { source with clock := source.clock - paid } := by
  classical
  let entered := bind source "node" root
  have dbNode : ofString "node" ≠ ofString "db" := by decide
  have hashNode : ofString "node" ≠ ofString "hash" := by decide
  have node' : entered.locals.lookup (ofString "node") = some (.val (.word root)) := by
    simp [entered, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have db' : entered.locals.lookup (ofString "db") = some (.val (.word table)) := by
    simp [entered, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, dbNode, db]
  have hash' : entered.locals.lookup (ofString "hash") = some (.val (.word hash)) := by
    simp [entered, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hashNode, hashLocal]
  have rep' := QueryMemory.represents_of_fields source entered rfl rfl rfl _ _ _ _ _ rep
  have view' := MemoryBytes.byteView_of_fields source entered rfl rfl rfl _ _ view
  obtain ⟨paid, bound, correct, frame⟩ := loop_execute tree entered table keys vals hash root query
    rep' node' db' hash' code view' fits little enough
  have tailResult := finish_loop entered _ paid correct frame
  have whole := declaration_return source "node" QueryEmpty.rootExpression tailCode root
    (valueOf (fastLookup ByteKeys.bit query tree)) paid
    (read_root source table root db rootMapped rootWord) tailResult.1 tailResult.2
  refine ⟨paid, bound, ?_⟩
  rw [QueryEmpty.body_shape]
  exact whole

/-- Instantiation for a built index: at most 262 source clocks, every key and
last-record-wins semantics. Constructing the memory representation and target
compiler/clock refinement are deliberately separate obligations. -/
theorem lookup_built {F : Type} (input : List (ByteKeys.Key × Graph.Slice))
    (source : PanSemStateFiniteExact 64 F) (table keys vals hash root : BitVec 64)
    (query : ByteKeys.Key)
    (rep : QueryMemory.Represents source table keys vals root (buildIndex ByteKeys.bit 256 input))
    (rootMapped : source.memaddrs (table + 24#64))
    (rootWord : source.memory (table + 24#64) = .word root)
    (db : source.locals.lookup (ofString "db") = some (.val (.word table)))
    (hashLocal : source.locals.lookup (ofString "hash") = some (.val (.word hash)))
    (code : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (view : MemoryBytes.ByteView source hash query)
    (fits : hash.toNat + 32 < 2 ^ 64) (little : source.be = false) (enough : 262 ≤ source.clock) :
    ∃ paid, paid ≤ 262 ∧
      (evaluateHOLFiniteState source QueryEmpty.body).1 = some (.returned (valueOf (lastValue query input))) ∧
      emptyLocalsHOLFinite (evaluateHOLFiniteState source QueryEmpty.body).2 =
        emptyLocalsHOLFinite { source with clock := source.clock - paid } := by
  classical
  have compactBound := compactHeight_le (build ByteKeys.bit 0 256 input)
  have depthBound := height_build ByteKeys.bit 0 256 input
  have heightBound : compactHeight (buildIndex ByteKeys.bit 256 input) ≤ 256 := by
    change compactHeight (compact (build ByteKeys.bit 0 256 input)) ≤ 256
    omega
  obtain ⟨paid, bound, returned, frame⟩ := lookup_tree _ source table keys vals hash root query rep
    rootMapped rootWord db hashLocal code view fits little (by omega)
  rw [ByteKeys.lookup] at returned
  exact ⟨paid, by omega, returned, frame⟩

end InitECandidate.Solver.WitnessRadix.QueryExecution

#print axioms InitECandidate.Solver.WitnessRadix.QueryExecution.lookup_tree
#print axioms InitECandidate.Solver.WitnessRadix.QueryExecution.lookup_built
