import InitECandidate.Solver.Input.CallResume

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem continuation_lookup_same {F : Type} (source target : PanSemStateFiniteExact 64 F) (name : String) (value : ValueHOL 64) :
    (continuationEntry source target name value).locals.lookup (ofString name)=some value := by
  simp [continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]

theorem continuation_lookup_other {F : Type} (source target : PanSemStateFiniteExact 64 F) (name other : String) (value : ValueHOL 64)
    (different : ofString name≠ofString other) :
    (continuationEntry source target name value).locals.lookup (ofString other)=source.locals.lookup (ofString other) := by
  simp [continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different]

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.continuation_lookup_same
#print axioms InitECandidate.Solver.Input.CallNormal.continuation_lookup_other
