import InitECandidate.Solver.Input.ReturnFacts
import InitECandidate.Solver.Input.LocalEffectsCall

namespace InitECandidate.Solver.Input.ReturnFacts
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

/-- A reached original read-only callee derives the frame used by its real
continuation. Failed calls cannot manufacture a caller return. -/
theorem scoped_readonly (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64))
    (formals : List (MlS × ShapeHOL)) (body continuation : ProgHOL 64) (returnShape : ShapeHOL)
    (known : source.code.lookup function=some (formals,body,returnShape))
    (pureBody : LocalEffects.Preserves source.code body) (property : ValueHOL 64 → Prop)
    (tail : ∀ target returned,LocalEffects.erase target=LocalEffects.erase source →
      Returns (CallNormal.continuationEntry source target name returned) continuation property) :
    Returns source (.decCall (Flapjack.Basis.Pure.MlString.ofString name) shape function arguments continuation) property := by
  intro post value normal
  obtain ⟨positive,values,actualBody,callee,actualShape,target,returned,inner,args,called,bodyRun,checked,continuationRun,restored⟩ :=
    CallNormal.scoped_data source post name shape function arguments continuation value normal
  have bodyEq := LocalEffects.lookup_body source.code function formals body returnShape known values actualBody callee actualShape called
  rw [bodyEq] at bodyRun
  have fields := pureBody (callEntryStateHOLFinite source callee) rfl
  rw [bodyRun] at fields
  exact tail target returned fields inner value continuationRun

end InitECandidate.Solver.Input.ReturnFacts

#print axioms InitECandidate.Solver.Input.ReturnFacts.scoped_readonly
