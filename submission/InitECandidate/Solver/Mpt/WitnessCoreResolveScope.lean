import InitECandidate.Solver.Mpt.WitnessCoreResolveState
import InitECandidate.Solver.Input.ScopeLookup

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The two actual lexical restorations around the original resolver.
These are analysis names for the real caller scopes, not runtime changes. -/
def resolveScoped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array : BitVec 64)
    (target : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  restore source "arr" (restore (QueryBranch.bind source "arr" array) "r" target)

theorem resolve_scoped_other (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (array : BitVec 64)
    (name : String) (notArray : ofString "arr"≠ofString name) (notResult : ofString "r"≠ofString name) :
    (resolveScoped source array target).locals.lookup (ofString name)=target.locals.lookup (ofString name) :=
  (Input.ScalarScope.restore_other source _ "arr" name notArray).trans
    (Input.ScalarScope.restore_other _ target "r" name notResult)

theorem resolve_scoped_terminal_fields (source ready : PanSemStateFiniteExact 64 Guest.HostMemory) (array record node : BitVec 64) :
    let current:=resolveScoped source array (resolvedTerminal ready record node)
    current.locals.lookup (ofString "result")=some (.val (.word node)) ∧
      current.locals.lookup (ofString "mode")=some (.val (.word 0#64)) ∧
      current.memory (record+80#64)=.word 0#64 ∧ current.globals=ready.globals ∧ current.clock=ready.clock := by
  have actual:=resolved_terminal_fields ready record node
  exact ⟨(resolve_scoped_other source _ array "result" (by decide) (by decide)).trans actual.1,
    (resolve_scoped_other source _ array "mode" (by decide) (by decide)).trans actual.2.1,actual.2.2.1,rfl,rfl⟩

theorem resolve_scoped_decode_fields (source ready : PanSemStateFiniteExact 64 Guest.HostMemory) (array record pointer length hash : BitVec 64) :
    let current:=resolveScoped source array (resolvedDecode ready record pointer length hash)
    current.locals.lookup (ofString "cur_p")=some (.val (.word pointer)) ∧
      current.locals.lookup (ofString "cur_n")=some (.val (.word length)) ∧
      current.locals.lookup (ofString "mode")=some (.val (.word 1#64)) ∧
      current.memory (record+80#64)=.word hash ∧ current.globals=ready.globals ∧ current.clock=ready.clock := by
  have actual:=resolved_decode_fields ready record pointer length hash
  exact ⟨(resolve_scoped_other source _ array "cur_p" (by decide) (by decide)).trans actual.1,
    (resolve_scoped_other source _ array "cur_n" (by decide) (by decide)).trans actual.2.1,
    (resolve_scoped_other source _ array "mode" (by decide) (by decide)).trans actual.2.2.1,actual.2.2.2.1,rfl,rfl⟩

theorem resolve_scoped_terminal_other (source ready : PanSemStateFiniteExact 64 Guest.HostMemory) (array record node : BitVec 64)
    (name : String) (notArray : ofString "arr"≠ofString name) (notR : ofString "r"≠ofString name)
    (notResult : ofString "result"≠ofString name) (notMode : ofString "mode"≠ofString name) :
    (resolveScoped source array (resolvedTerminal ready record node)).locals.lookup (ofString name)=ready.locals.lookup (ofString name) :=
  (resolve_scoped_other source _ array name notArray notR).trans (resolved_terminal_other ready record node name notResult notMode)

theorem resolve_scoped_decode_other (source ready : PanSemStateFiniteExact 64 Guest.HostMemory) (array record pointer length hash : BitVec 64)
    (name : String) (notArray : ofString "arr"≠ofString name) (notR : ofString "r"≠ofString name)
    (notPointer : ofString "cur_p"≠ofString name) (notLength : ofString "cur_n"≠ofString name) (notMode : ofString "mode"≠ofString name) :
    (resolveScoped source array (resolvedDecode ready record pointer length hash)).locals.lookup (ofString name)=ready.locals.lookup (ofString name) :=
  (resolve_scoped_other source _ array name notArray notR).trans (resolved_decode_other ready record pointer length hash name notPointer notLength notMode)

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.resolve_scoped_other
#print axioms InitECandidate.Solver.Mpt.WitnessCore.resolve_scoped_terminal_fields
#print axioms InitECandidate.Solver.Mpt.WitnessCore.resolve_scoped_decode_fields
#print axioms InitECandidate.Solver.Mpt.WitnessCore.resolve_scoped_terminal_other
#print axioms InitECandidate.Solver.Mpt.WitnessCore.resolve_scoped_decode_other
