import InitECandidate.Solver.Rlp.ValidationArena
import InitECandidate.Solver.Rlp.ItemSyntax
import InitECandidate.Solver.Input.CurrentStartup.ArenaFrame
import InitECandidate.Solver.Input.ClockCostGuardReached
import InitECandidate.Solver.Input.ClockCostScopedReached

namespace InitECandidate.Solver.Rlp.CurrentItem
open Flapjack PanSemStateFiniteExact
open Item
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def kindOf : ValueHOL 64 → Option (BitVec 64)
  | .rStruct (.val (.word flag) :: _) => some flag
  | _ => none

/-- A returned item parser retains runtime metadata and all memory outside
its temporary scratch interval. -/
structure Frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  metadata : Input.MemoryMetadata.erase target=Input.MemoryMetadata.erase source
  outside : Validation.Outside source target 2952790016 2965299200

theorem Frame.of_readonly {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (pure : Input.LocalEffects.erase target=Input.LocalEffects.erase source) : Frame source target :=
  ⟨Input.MemoryMetadata.of_frame pure,Validation.Outside.of_readonly 2952790016 2965299200 pure⟩

theorem Frame.trans {source middle target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (last : Frame middle target) (first : Frame source middle) : Frame source target :=
  ⟨last.metadata.trans first.metadata,⟨last.outside.runtime.trans first.outside.runtime,
    fun query outsideQuery=>(last.outside query outsideQuery).trans (first.outside query outsideQuery)⟩⟩

/-- Local scopes, clock changes and actual readonly reader prefixes transport
this frame without asserting equality of the temporary scratch bytes. -/
theorem Frame.of_erase {source target entry exit : PanSemStateFiniteExact 64 Guest.HostMemory}
    (data : Frame source target)
    (before : Input.LocalEffects.erase entry=Input.LocalEffects.erase source)
    (after : Input.LocalEffects.erase exit=Input.LocalEffects.erase target) : Frame entry exit := by
  have metadata := (Input.MemoryMetadata.of_frame after).trans
    (data.metadata.trans (Input.MemoryMetadata.of_frame before).symm)
  have runtime := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>
    {state with globals:=HolFiniteMapExact.empty}) metadata
  have input := Input.LocalEffects.memory_of_erase source entry before
  have output := Input.LocalEffects.memory_of_erase target exit after
  exact ⟨metadata,⟨runtime,fun query outsideQuery=>(congrFun output query).trans
    ((data.outside query outsideQuery).trans (congrFun input query).symm)⟩⟩

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

#print axioms InitECandidate.Solver.Rlp.CurrentItem.Frame.of_readonly
#print axioms InitECandidate.Solver.Rlp.CurrentItem.Frame.trans
#print axioms InitECandidate.Solver.Rlp.CurrentItem.Frame.of_erase
