import InitECandidate.Solver.Rlp.ItemProgram
import InitECandidate.Solver.Input.ClockCostGuardReached
import InitECandidate.Solver.Input.ClockCostScopedReached

namespace InitECandidate.Solver.Rlp.Item
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure Entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64) : Prop where
  pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer))
  lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length))
  arena : Validation.Arena source cursor limit
  nonempty : 1≤length.toNat
  fits : pointer.toNat+length.toNat<2^64

theorem Entry.bound_word (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit word : BitVec 64)
    (name : String) (entry : Entry source pointer length cursor limit)
    (notP : ofString name≠ofString "p") (notLen : ofString name≠ofString "len") :
    Entry (bind source name word) pointer length cursor limit :=
  ⟨(bind_lookup_other source name "p" word notP).trans entry.pointerCell,
    (bind_lookup_other source name "len" word notLen).trans entry.lengthCell,
    Validation.Arena.of_fields source _ cursor limit entry.arena rfl rfl,entry.nonempty,entry.fits⟩

theorem Entry.readonly_resume (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (name : String) (value : ValueHOL 64) (entry : Entry source pointer length cursor limit)
    (fields : Input.LocalEffects.erase target=Input.LocalEffects.erase source)
    (notP : ofString "p"≠ofString name) (notLen : ofString "len"≠ofString name) :
    Entry (Input.CallNormal.continuationEntry source target name value) pointer length cursor limit := by
  let ready := Input.CallNormal.continuationEntry source target name value
  have other (key : String) (different : ofString key≠ofString name) :
      ready.locals.lookup (ofString key)=source.locals.lookup (ofString key) := by
    simp [ready,Input.CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different,Ne.symm different]
  refine ⟨(other "p" notP).trans entry.pointerCell,(other "len" notLen).trans entry.lengthCell,
    Validation.Arena.of_fields source ready cursor limit entry.arena ?_ ?_,entry.nonempty,entry.fits⟩
  · have domain := congrArg PanSemStateFiniteExact.memaddrs fields
    exact domain
  · have globals := congrArg PanSemStateFiniteExact.globals fields
    exact globals

end InitECandidate.Solver.Rlp.Item

#print axioms InitECandidate.Solver.Rlp.Item.Entry.bound_word
#print axioms InitECandidate.Solver.Rlp.Item.Entry.readonly_resume
