import InitECandidate.Solver.Headers.FieldStore

namespace InitECandidate.Solver.Headers
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Ordinary words between scratch and the new output header are retained.
This protects preceding decoded data and earlier headers, not just the
currently selected RLP input or its record array. -/
def FieldMemory (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cutoff : Nat) (header : BitVec 64) : Prop :=
  ∀ query,cutoff≤query.toNat → query.toNat<header.toNat → target.memory query=source.memory query

theorem FieldMemory.refl (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cutoff : Nat) (header : BitVec 64) :
    FieldMemory source source cutoff header := fun _ _ _=>rfl

theorem FieldMemory.trans (source middle target : PanSemStateFiniteExact 64 Guest.HostMemory) (cutoff : Nat) (header : BitVec 64)
    (first : FieldMemory source middle cutoff header) (second : FieldMemory middle target cutoff header) : FieldMemory source target cutoff header :=
  fun query lower upper=>(second query lower upper).trans (first query lower upper)

theorem FieldState.store_memory (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer array header cursor limit current : BitVec 64) (bytes cutoff : Nat) (items : List Rlp.ListItem) (active : List Slot)
    (state : FieldState source pointer array header cursor limit current bytes cutoff items active)
    (offset : Nat) (value : StoreValue) (ready : value.Ready active) (within : offset+8*value.words≤248)
    (normal : evaluateHOLFiniteState source (storeProgram offset value)=(none,target)) : FieldMemory source target cutoff header := by
  obtain ⟨actual,valueRead,size⟩ := value.read source active state.slots current state.currentCell ready
  have addressRead : eval source (storeAddress offset)=some (.val (.word (header+BitVec.ofNat 64 offset))) := by
    simp [storeAddress,eval,evalHOLExact,evalListHOLExact,toExact,state.headerCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have number : (header+BitVec.ofNat 64 offset).toNat=header.toNat+offset :=
    MemoryBytes.offset_toNat header offset (by have h:=state.headerArena.upper; omega)
  obtain ⟨observed,memory,read,stores,post⟩ := Input.store_at_normal source target (storeAddress offset) value.expression (header+BitVec.ofNat 64 offset) addressRead normal
  have same : observed=actual := Option.some.inj (read.symm.trans valueRead)
  subst observed
  intro query lower upper
  rw [post]
  apply Input.words_away (flattenHOL actual) (header+BitVec.ofNat 64 offset) query source.memaddrs source.memory memory stores
  intro index inside equal
  have atWord : ((header+BitVec.ofNat 64 offset)+BitVec.ofNat 64 (8*index)).toNat=header.toNat+offset+8*index := by
    rw [MemoryBytes.offset_toNat _ (8*index) (by rw [number]; have h:=state.headerArena.upper; rw [size] at inside; omega),number]
  have same:=congrArg BitVec.toNat equal
  rw [atWord] at same
  omega

end InitECandidate.Solver.Headers

#print axioms InitECandidate.Solver.Headers.FieldMemory.refl
#print axioms InitECandidate.Solver.Headers.FieldMemory.trans
#print axioms InitECandidate.Solver.Headers.FieldState.store_memory
