import InitECandidate.Solver.Input.ContinuingDeclarationEntry
import InitECandidate.Solver.Input.MemoryNormal
import InitECandidate.Solver.Input.NoneControl

namespace InitECandidate.Solver.Input.MemoryAt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem sequence_normal {F : Type} (source post : PanSemStateFiniteExact 64 F) (first second : ProgHOL 64) (query : BitVec 64)
    (front : ∀ middle,evaluateHOLFiniteState source first=(none,middle) → middle.memory query=source.memory query)
    (back : ∀ middle,evaluateHOLFiniteState source first=(none,middle) → evaluateHOLFiniteState middle second=(none,post) → post.memory query=middle.memory query)
    (run : evaluateHOLFiniteState source (.seq first second)=(none,post)) : post.memory query=source.memory query := by
  obtain ⟨middle,normal,remaining⟩ := sequence_none source post first second run
  exact (back middle normal remaining).trans (front middle normal)

theorem declaration_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (shape : ShapeHOL) (expression : ExpHOL 64) (body : ProgHOL 64) (query : BitVec 64)
    (frame : ∀ declared inner,evaluateHOLFiniteState (setVarHOLFinite (ofString name) declared source) body=(none,inner) → inner.memory query=source.memory query)
    (run : evaluateHOLFiniteState source (.dec (ofString name) shape expression body)=(none,post)) : post.memory query=source.memory query := by
  obtain ⟨declared,inner,read,typed,remaining,endpoint⟩ := CallNormal.declaration_continuing_entry source post name shape expression body run
  rw [endpoint]
  exact frame declared inner remaining

theorem assign_current {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : VarKind) (name : MlS) (expression : ExpHOL 64) (query : BitVec 64) :
    (evaluateHOLFiniteState source (.assign kind name expression)).2.memory query=source.memory query := by
  rw [evaluateHOLFiniteState_assign]
  split
  · rfl
  · split
    · cases kind <;> rfl
    · rfl

theorem return_current {F : Type} (source : PanSemStateFiniteExact 64 F) (expression : ExpHOL 64) (query : BitVec 64) :
    (evaluateHOLFiniteState source (.return expression)).2.memory query=source.memory query := by
  rw [evaluateHOLFiniteState_return]
  split
  · rfl
  · split <;> rfl

theorem set_lookup_other {F : Type} (source : PanSemStateFiniteExact 64 F) (name key : MlS) (value : ValueHOL 64) (different : name≠key) :
    (setVarHOLFinite name value source).locals.lookup key=source.locals.lookup key := by
  simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,Ne.symm different]

end InitECandidate.Solver.Input.MemoryAt

#print axioms InitECandidate.Solver.Input.MemoryAt.sequence_normal
#print axioms InitECandidate.Solver.Input.MemoryAt.declaration_normal
#print axioms InitECandidate.Solver.Input.MemoryAt.assign_current
#print axioms InitECandidate.Solver.Input.MemoryAt.return_current
#print axioms InitECandidate.Solver.Input.MemoryAt.set_lookup_other
