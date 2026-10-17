import InitECandidate.Solver.Input.LocalPrefix
import InitECandidate.Solver.Input.NormalDeclarationEntry

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A selected continuation inside real caller scopes. The path may cross
arbitrary helper calls and local-preserving normal prefixes. -/
inductive LocalPath (key : String) (target : ProgHOL 64) : ProgHOL 64 → Prop where
  | here : LocalPath key target target
  | seq (front : ProgHOL 64) {rest : ProgHOL 64}
      (safe : LocalPrefix (ofString key) front) (tail : LocalPath key target rest) :
      LocalPath key target (.seq front rest)
  | dec (name : String) (shape : ShapeHOL) (expression : ExpHOL 64) {rest : ProgHOL 64}
      (other : ofString key ≠ ofString name) (tail : LocalPath key target rest) :
      LocalPath key target (.dec (ofString name) shape expression rest)
  | decCall (name : String) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64))
      {rest : ProgHOL 64} (other : ofString key ≠ ofString name) (tail : LocalPath key target rest) :
      LocalPath key target (.decCall (ofString name) shape function arguments rest)

/-- Normal execution reaches the selected suffix with the saved binding and
canonical code/exception tables intact. No helper return/read/clock hypotheses
are needed. This is a reachability fact, not a cost for the prefix. -/
theorem LocalPath.normal_reaches {key : String} {target program : ProgHOL 64}
    (path : LocalPath key target program) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source program = (some (.returned value), post)) :
    ∃ ready finish : PanSemStateFiniteExact 64 Guest.HostMemory, evaluateHOLFiniteState ready target = (some (.returned value), finish) ∧
      ready.locals.lookup (ofString key) = source.locals.lookup (ofString key) ∧
      ready.code = source.code ∧ ready.eshapes = source.eshapes := by
  classical
  induction path generalizing source post with
  | here => exact ⟨source, post, run, rfl, rfl, rfl⟩
  | seq front safe tail ih =>
    obtain ⟨middle, firstRun, restRun, sameLocal⟩ := safe.normal_continue source post _ value run
    obtain ⟨ready, finish, suffixRun, localEq, codes, shapes⟩ := ih middle post restRun
    have fields := evaluation_fields source middle front none firstRun
    exact ⟨ready, finish, suffixRun, localEq.trans sameLocal, codes.trans fields.2.2.2,
      shapes.trans fields.2.2.1⟩
  | dec name shape expression other tail ih =>
    obtain ⟨declared, inner, read, typed, restRun, restored⟩ :=
      CallNormal.declaration_normal_entry source post name shape expression _ value run
    obtain ⟨ready, finish, suffixRun, localEq, codes, shapes⟩ := ih _ inner restRun
    have sameLocal : (setVarHOLFinite (ofString name) declared source).locals.lookup (ofString key) =
        source.locals.lookup (ofString key) := by
      simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, other, Ne.symm other]
    exact ⟨ready, finish, suffixRun, localEq.trans sameLocal, codes, shapes⟩
  | decCall name shape function arguments other tail ih =>
    obtain ⟨calleePost, returned, inner, restRun, restored, domain, endian, shapes, codes, typed⟩ :=
      CallNormal.normal_entry source post name shape function arguments _ value run
    obtain ⟨ready, finish, suffixRun, localEq, nextCodes, nextShapes⟩ := ih _ inner restRun
    have sameLocal : (CallNormal.continuationEntry source calleePost name returned).locals.lookup (ofString key) =
        source.locals.lookup (ofString key) := by
      simp [CallNormal.continuationEntry, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, other, Ne.symm other]
    exact ⟨ready, finish, suffixRun, localEq.trans sameLocal, nextCodes.trans codes, nextShapes.trans shapes⟩

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.LocalPath.normal_reaches
