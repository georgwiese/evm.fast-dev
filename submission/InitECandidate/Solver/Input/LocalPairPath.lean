import InitECandidate.Solver.Input.LocalPathTactics

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A single actual caller path retaining two saved bindings. Both locals
refer to the same reached state, rather than separate existential witnesses. -/
inductive LocalPairPath (left right : String) (target : ProgHOL 64) : ProgHOL 64 → Prop where
  | here : LocalPairPath left right target target
  | seq (front : ProgHOL 64) {rest : ProgHOL 64}
      (first : LocalPrefix (ofString left) front) (second : LocalPrefix (ofString right) front)
      (tail : LocalPairPath left right target rest) : LocalPairPath left right target (.seq front rest)
  | dec (name : String) (shape : ShapeHOL) (expression : ExpHOL 64) {rest : ProgHOL 64}
      (first : ofString left ≠ ofString name) (second : ofString right ≠ ofString name)
      (tail : LocalPairPath left right target rest) : LocalPairPath left right target (.dec (ofString name) shape expression rest)
  | decCall (name : String) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64)) {rest : ProgHOL 64}
      (first : ofString left ≠ ofString name) (second : ofString right ≠ ofString name)
      (tail : LocalPairPath left right target rest) : LocalPairPath left right target (.decCall (ofString name) shape function arguments rest)

theorem LocalPairPath.normal_reaches {left right : String} {target program : ProgHOL 64}
    (path : LocalPairPath left right target program) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source program = (some (.returned value), post)) :
    ∃ ready finish : PanSemStateFiniteExact 64 Guest.HostMemory,
      evaluateHOLFiniteState ready target = (some (.returned value), finish) ∧
      ready.locals.lookup (ofString left) = source.locals.lookup (ofString left) ∧
      ready.locals.lookup (ofString right) = source.locals.lookup (ofString right) ∧
      ready.code = source.code ∧ ready.eshapes = source.eshapes := by
  classical
  induction path generalizing source post with
  | here => exact ⟨source, post, normal, rfl, rfl, rfl, rfl⟩
  | seq front first second tail ih =>
    obtain ⟨middle, firstRun, restRun, firstLocal⟩ := first.normal_continue source post _ value normal
    have other := second.summary source
    rw [firstRun] at other
    have secondLocal := other.1 rfl
    obtain ⟨ready, finish, run, leftEq, rightEq, codes, shapes⟩ := ih middle post restRun
    have fields := evaluation_fields source middle front none firstRun
    exact ⟨ready, finish, run, leftEq.trans firstLocal, rightEq.trans secondLocal, codes.trans fields.2.2.2, shapes.trans fields.2.2.1⟩
  | dec name shape expression first second tail ih =>
    obtain ⟨declared, inner, read, typed, restRun, restored⟩ := CallNormal.declaration_normal_entry source post name shape expression _ value normal
    obtain ⟨ready, finish, run, leftEq, rightEq, codes, shapes⟩ := ih _ inner restRun
    have firstLocal : (setVarHOLFinite (ofString name) declared source).locals.lookup (ofString left) = source.locals.lookup (ofString left) := by
      simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, first, Ne.symm first]
    have secondLocal : (setVarHOLFinite (ofString name) declared source).locals.lookup (ofString right) = source.locals.lookup (ofString right) := by
      simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, second, Ne.symm second]
    exact ⟨ready, finish, run, leftEq.trans firstLocal, rightEq.trans secondLocal, codes, shapes⟩
  | decCall name shape function arguments first second tail ih =>
    obtain ⟨calleePost, returned, inner, restRun, restored, domain, endian, shapes, codes, typed⟩ := CallNormal.normal_entry source post name shape function arguments _ value normal
    obtain ⟨ready, finish, run, leftEq, rightEq, nextCodes, nextShapes⟩ := ih _ inner restRun
    have firstLocal : (CallNormal.continuationEntry source calleePost name returned).locals.lookup (ofString left) = source.locals.lookup (ofString left) := by
      simp [CallNormal.continuationEntry, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, first, Ne.symm first]
    have secondLocal : (CallNormal.continuationEntry source calleePost name returned).locals.lookup (ofString right) = source.locals.lookup (ofString right) := by
      simp [CallNormal.continuationEntry, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, second, Ne.symm second]
    exact ⟨ready, finish, run, leftEq.trans firstLocal, rightEq.trans secondLocal, nextCodes.trans codes, nextShapes.trans shapes⟩

syntax "prove_local_pair_path" : tactic
macro_rules
  | `(tactic| prove_local_pair_path) => `(tactic|
      first
      | exact LocalPairPath.here
      | apply LocalPairPath.seq
        · prove_local_prefix
        · prove_local_prefix
        · prove_local_pair_path
      | apply LocalPairPath.dec _ _ _ (by decide) (by decide)
        prove_local_pair_path
      | apply LocalPairPath.decCall _ _ _ _ (by decide) (by decide)
        prove_local_pair_path)

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.LocalPairPath.normal_reaches
