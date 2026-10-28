import InitECandidate.Solver.Input.CurrentTable.NewStores
import InitECandidate.Solver.Input.CurrentAllocationTrace

namespace InitECandidate.Solver.Input.CurrentTable.New
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def arrayEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cursor amount : BitVec 64) (name : String) (offset : Nat) :=
  putField (bind (PersistentAlloc.post {source with clock:=source.clock-1} cursor amount) name cursor) table offset cursor

/-- One of the actual current keys/nodes/order allocation scopes followed
by its table-pointer store. A genuine return derives room; the fixed mapped
table field then executes and exposes the original continuation. -/
theorem array_allocation_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table cursor amount : BitVec 64) (name : String) (offset : Nat) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (different : ofString name≠ofString "t") (inside : offset<88) (offsetAligned : offset%8=0)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena table 88) (aligned : table.toNat%8=0)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (PersistentAlloc.values amount))
    (installed : OriginalCode.Installed source.code)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor))) (heapBound : cursor.toNat≤2952790016)
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "alloc") arguments
      (.seq (.store (Scalar.plus (localVar "t") offset) (localVar name)) continuation))=(outcome,post)) :
    (source.clock-post.clock≤2 ∧ ∀ value,outcome≠some (.returned value)) ∨ 1≤source.clock ∧ cursor.toNat+amount.toNat≤2952790016 ∧
      ∃ inner,evaluateHOLFiniteState (arrayEntry source table cursor amount name offset) continuation=(outcome,inner) ∧ post=restore source name inner := by
  rcases CurrentAlloc.scoped_classified source post name arguments (.seq (.store (Scalar.plus (localVar "t") offset) (localVar name)) continuation)
    cursor amount args installed heapCell heapBound outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨funded,room,inner,continued,endpoint⟩:=reached
    let ready:=bind (PersistentAlloc.post {source with clock:=source.clock-1} cursor amount) name cursor
    have tableNext : ready.locals.lookup (ofString "t")=some (.val (.word table)) :=
      (bind_lookup_other _ name "t" cursor different).trans tableCell
    have valueRead : eval ready (localVar name)=some (.val (.word cursor)) := Request.local_word ready name cursor (bind_lookup_same _ _ _)
    have stored:=store_field ready table cursor offset (localVar name) domain arena aligned inside offsetAligned tableNext valueRead
    change evaluateHOLFiniteState ready (.seq (.store (Scalar.plus (localVar "t") offset) (localVar name)) continuation)=(outcome,inner) at continued
    rw [evaluateHOLFiniteState_seq_line780,stored] at continued
    exact Or.inr ⟨funded,room,inner,continued,endpoint⟩

/-- The reached array/pointer-store state retains caller locals, every
nonheap global and every memory word outside the one header field. -/
theorem array_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cursor amount : BitVec 64) (name : String) (offset : Nat) :
    (arrayEntry source table cursor amount name offset).globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded cursor amount))) ∧
    (arrayEntry source table cursor amount name offset).clock=source.clock-1 ∧
    (∀ key : MlS,key≠ofString name→(arrayEntry source table cursor amount name offset).locals.lookup key=source.locals.lookup key) ∧
    (∀ key : MlS,key≠ofString "heap_ptr"→(arrayEntry source table cursor amount name offset).globals.lookup key=source.globals.lookup key) ∧
    (∀ query : BitVec 64,query≠table+BitVec.ofNat 64 offset→(arrayEntry source table cursor amount name offset).memory query=source.memory query) := by
  refine ⟨?_,rfl,?_,?_,?_⟩
  · simp [arrayEntry,putField,WitnessRadix.QueryBranch.bind,setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE]
  · intro key different
    simp [arrayEntry,putField,WitnessRadix.QueryBranch.bind,setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,Ne.symm different]
  · intro key different
    simp [arrayEntry,putField,WitnessRadix.QueryBranch.bind,setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,Ne.symm different]
  · intro query different
    simp [arrayEntry,putField,StoreWord.put,different,WitnessRadix.QueryBranch.bind,setVarHOLFinite,PersistentAlloc.post]

end InitECandidate.Solver.Input.CurrentTable.New

#print axioms InitECandidate.Solver.Input.CurrentTable.New.array_allocation_trace

#print axioms InitECandidate.Solver.Input.CurrentTable.New.array_frame
