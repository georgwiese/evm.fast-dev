import InitECandidate.Solver.Input.RunAttemptConstructorInputs
import InitECandidate.Solver.Input.RunAttemptHeaderPrefix

namespace InitECandidate.Solver.Input.RunAttempt
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Projection facts are checked at a generic state, before actual nested
caller states are substituted into the whole-prefix composition. -/
theorem constructor_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count hashes : BitVec 64) (parent : ValueHOL 64) :
    (constructorEntry source count hashes parent).memory=source.memory := rfl

theorem constructor_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count hashes : BitVec 64) (parent : ValueHOL 64) :
    (constructorEntry source count hashes parent).clock=source.clock := rfl

theorem constructor_si (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count hashes si : BitVec 64) (parent : ValueHOL 64)
    (cell : source.locals.lookup (ofString "si")=some (.val (.word si))) :
    (constructorEntry source count hashes parent).locals.lookup (ofString "si")=some (.val (.word si)) := by
  simp only [constructorEntry,putGlobal,parentEntry,countEntry,WitnessRadix.QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  exact cell

theorem restoreHeader_clock (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (payload : BitVec 64) :
    (restoreHeader source payload target).clock=target.clock := rfl

theorem restoreConstructor_clock (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (count : BitVec 64) :
    (restoreConstructor source count target).clock=target.clock := rfl

theorem headerEntry_si (source : PanSemStateFiniteExact 64 Guest.HostMemory) (payload si : BitVec 64)
    (cell : source.locals.lookup (ofString "si")=some (.val (.word si))) :
    (headerEntry source payload).locals.lookup (ofString "si")=some (.val (.word si)) :=
  (bind_lookup_other source "pl" "si" payload (by decide)).trans cell

end InitECandidate.Solver.Input.RunAttempt

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem continuation_memory (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (value : ValueHOL 64) :
    (continuationEntry source target name value).memory=target.memory := rfl

theorem continuation_clock (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (value : ValueHOL 64) :
    (continuationEntry source target name value).clock=target.clock := rfl

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.RunAttempt.constructor_memory
#print axioms InitECandidate.Solver.Input.RunAttempt.constructor_clock
#print axioms InitECandidate.Solver.Input.RunAttempt.constructor_si
#print axioms InitECandidate.Solver.Input.RunAttempt.restoreHeader_clock
#print axioms InitECandidate.Solver.Input.RunAttempt.restoreConstructor_clock
#print axioms InitECandidate.Solver.Input.RunAttempt.headerEntry_si
#print axioms InitECandidate.Solver.Input.CallNormal.continuation_memory
#print axioms InitECandidate.Solver.Input.CallNormal.continuation_clock
