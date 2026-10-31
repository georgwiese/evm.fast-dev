import InitECandidate.Solver.Mpt.WitnessCoreStackReturn
import InitECandidate.Solver.Mpt.WitnessCoreLoopFields
import InitECandidate.Solver.Input.CurrentTable.NodeLookup.Returned

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Active allocations follow the fixed heap frontier at materializer
entry. This frontier does not move when old MPT nodes are updated. -/
def FreshFrom (frontier : Nat) (stack : List Entry) : Prop:=
  ∀ entry∈stack,frontier≤entry.data.array.toNat ∧ frontier≤entry.data.payload.startAddress

/-- Every waiting activation has actually passed through its resolver
and therefore has an initialized pending HASH. A freshly pushed current
activation may remain uninitialized until its first resolver iteration. -/
def Waiting (stack : List Entry) : Prop:=∀ entry∈stack,∃ hash,entry.pending=some hash

theorem FreshFrom.tail (frontier : Nat) (entry : Entry) (rest : List Entry) (fresh : FreshFrom frontier (entry::rest)) : FreshFrom frontier rest:=
  fun parent member=>fresh parent (List.mem_cons_of_mem _ member)

theorem Waiting.tail (entry : Entry) (rest : List Entry) (waiting : Waiting (entry::rest)) : Waiting rest:=
  fun parent member=>waiting parent (List.mem_cons_of_mem _ member)

theorem FreshFrom.cons (frontier : Nat) (entry : Entry) (rest : List Entry) (fresh : FreshFrom frontier rest)
    (array : frontier≤entry.data.array.toNat) (payload : frontier≤entry.data.payload.startAddress) : FreshFrom frontier (entry::rest) := by
  intro current member
  rcases List.mem_cons.mp member with rfl|older
  · exact ⟨array,payload⟩
  · exact fresh current older

theorem FreshFrom.advance (frontier : Nat) (entry next : Entry) (rest : List Entry) (fresh : FreshFrom frontier (entry::rest))
    (array : next.data.array=entry.data.array) (payload : next.data.payload.startAddress=entry.data.payload.startAddress) : FreshFrom frontier (next::rest) :=
  (fresh.tail frontier entry rest).cons frontier next rest (by rw [array]; exact (fresh entry List.mem_cons_self).1)
    (by rw [payload]; exact (fresh entry List.mem_cons_self).2)

theorem Waiting.cons (entry : Entry) (rest : List Entry) (waiting : Waiting rest) (pending : ∃ hash,entry.pending=some hash) : Waiting (entry::rest) := by
  intro current member
  rcases List.mem_cons.mp member with rfl|older
  · exact pending
  · exact waiting current older

theorem Waiting.advance (entry next : Entry) (rest : List Entry) (waiting : Waiting (entry::rest))
    (pending : next.pending=entry.pending) : Waiting (next::rest) :=
  (waiting.tail entry rest).cons next rest (by rw [pending]; exact waiting entry List.mem_cons_self)

theorem ReturnStep.data_words (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db heap cursor limit child slot : BitVec 64) (entry : Entry) (rest : List Entry)
    (step : ReturnStep source post db heap cursor limit child slot entry rest) (words : DataWords source) : DataWords post := by
  obtain ⟨next,nextCell,nextArena,nextBound,aligned,grows,scratch,nextLive,shape,globals,domain,endian,code,memory,locals⟩:=step
  obtain ⟨pointer,pointerCell⟩:=words.pointer
  obtain ⟨length,lengthCell⟩:=words.length
  have postPointer:= (locals "cur_p" (Or.inr (Or.inr (Or.inl rfl)))).trans pointerCell
  have postLength:= (locals "cur_n" (Or.inr (Or.inr (Or.inr rfl)))).trans lengthCell
  rcases shape with ⟨nextEntry,a,b,c,d,e,view,top,actualSlot,mode,result,rank⟩|⟨view,node,owned,top,result,mode,actualSlot,rank⟩
  · exact ⟨⟨pointer,postPointer⟩,⟨length,postLength⟩,⟨child,result⟩,⟨_,actualSlot⟩⟩
  · exact ⟨⟨pointer,postPointer⟩,⟨length,postLength⟩,⟨node,result⟩,⟨slot,actualSlot⟩⟩

/-- Return writes may update persistent parent nodes, but every active
allocation follows the fixed entry frontier. The genuine table and rows
below that frontier survive either advancing or popping the current head. -/
theorem ReturnStep.database (data : Input.CurrentTable.NodeBuild.Data)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frontier : Nat)
    (db heap cursor limit child slot : BitVec 64) (entry : Entry) (rest : List Entry)
    (database : Input.CurrentTable.NodeLookup.Database source data)
    (tableBefore : (Input.CurrentTable.New.endPointer data.table data.cap).toNat≤frontier)
    (fresh : FreshFrom frontier (entry::rest))
    (step : ReturnStep source post db heap cursor limit child slot entry rest) :
    Input.CurrentTable.NodeLookup.Database post data := by
  obtain ⟨next,nextCell,nextArena,nextBound,aligned,grows,scratch,nextLive,shape,globals,domain,endian,code,memory,locals⟩:=step
  apply database.of_before frontier tableBefore domain endian
  intro query earlier
  exact memory query (Or.inl (earlier.trans_le (fresh entry List.mem_cons_self).2))

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.FreshFrom.tail
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.Waiting.tail
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.FreshFrom.cons
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.FreshFrom.advance
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.Waiting.cons
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.Waiting.advance
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ReturnStep.data_words
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ReturnStep.database
