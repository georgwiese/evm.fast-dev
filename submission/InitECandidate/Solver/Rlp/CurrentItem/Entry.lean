import InitECandidate.Solver.Rlp.ItemSyntax
import InitECandidate.Solver.Input.CurrentStartup.ArenaFrame
import InitECandidate.Solver.Input.ClockCostGuardReached
import InitECandidate.Solver.Input.ClockCostScopedReached

namespace InitECandidate.Solver.Rlp.CurrentItem
open Flapjack PanSemStateFiniteExact
open Item
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure Entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64) : Prop where
  pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer))
  lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length))
  arena : Input.CurrentStartup.ArenaState source
  nonempty : 1≤length.toNat
  fits : pointer.toNat+length.toNat<2^64

theorem Entry.bound_word (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length word : BitVec 64)
    (name : String) (entry : Entry source pointer length)
    (notP : ofString name≠ofString "p") (notLen : ofString name≠ofString "len") :
    Entry (bind source name word) pointer length :=
  ⟨(bind_lookup_other source name "p" word notP).trans entry.pointerCell,
    (bind_lookup_other source name "len" word notLen).trans entry.lengthCell,
    entry.arena.of_frame rfl,entry.nonempty,entry.fits⟩

theorem Entry.readonly_resume (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (name : String) (value : ValueHOL 64) (entry : Entry source pointer length)
    (fields : Input.LocalEffects.erase target=Input.LocalEffects.erase source)
    (notP : ofString "p"≠ofString name) (notLen : ofString "len"≠ofString name) :
    Entry (Input.CallNormal.continuationEntry source target name value) pointer length := by
  let ready := Input.CallNormal.continuationEntry source target name value
  have other (key : String) (different : ofString key≠ofString name) :
      ready.locals.lookup (ofString key)=source.locals.lookup (ofString key) := by
    simp [ready,Input.CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different,Ne.symm different]
  refine ⟨(other "p" notP).trans entry.pointerCell,(other "len" notLen).trans entry.lengthCell,
    entry.arena.of_frame fields,entry.nonempty,entry.fits⟩

end InitECandidate.Solver.Rlp.CurrentItem

#print axioms InitECandidate.Solver.Rlp.CurrentItem.Entry.bound_word
#print axioms InitECandidate.Solver.Rlp.CurrentItem.Entry.readonly_resume
