import InitECandidate.Solver.Mpt.InsertEmptyChoice

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The real iteration prefix clears these four pending traversal fields
before its original node dispatch. -/
structure Pending (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  node : source.locals.lookup (ofString "next_node")=some (.val (.word 0#64))
  slot : source.locals.lookup (ofString "next_slot")=some (.val (.word 0#64))
  level : source.locals.lookup (ofString "next_level")=some (.val (.word 0#64))
  go : source.locals.lookup (ofString "go")=some (.val (.word 0#64))

theorem Pending.dispatch (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Pending (dispatchEntry source) := by
  constructor
  all_goals simp [dispatchEntry,prepared,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]

theorem Pending.after_scalar (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (word : BitVec 64)
    (pending : Pending source)
    (notNode : ofString "next_node"≠ofString name) (notSlot : ofString "next_slot"≠ofString name)
    (notLevel : ofString "next_level"≠ofString name) (notGo : ofString "go"≠ofString name)
    (localsEq : target.locals=source.locals.update (ofString name,.val (.word word))) : Pending target := by
  have current (query : MlS) (other : query≠ofString name) : target.locals.lookup query=source.locals.lookup query:=by
    rw [localsEq]
    simp [HolFiniteMapExact.update,FUPDATE,Ne.symm other]
  exact ⟨(current _ notNode).trans pending.node,(current _ notSlot).trans pending.slot,
    (current _ notLevel).trans pending.level,(current _ notGo).trans pending.go⟩

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.Pending.dispatch
#print axioms InitECandidate.Solver.Mpt.Insert.Pending.after_scalar
