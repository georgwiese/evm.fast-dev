import InitECandidate.Solver.Headers.CurrentPipeline.Store

namespace InitECandidate.Solver.Headers.CurrentPipeline
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def BeforeMemory (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (header : BitVec 64) : Prop :=
  ∀ query,query.toNat<header.toNat → target.memory query=source.memory query

theorem BeforeMemory.refl (source : PanSemStateFiniteExact 64 Guest.HostMemory) (header : BitVec 64) :
    BeforeMemory source source header := fun _ _=>rfl

theorem BeforeMemory.trans (source middle target : PanSemStateFiniteExact 64 Guest.HostMemory) (header : BitVec 64)
    (first : BeforeMemory source middle header) (second : BeforeMemory middle target header) : BeforeMemory source target header :=
  fun query upper=>(second query upper).trans (first query upper)

theorem State.store_memory (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer array header current : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem) (active : List Slot)
    (state : State source pointer array header current bytes items active)
    (offset : Nat) (value : StoreValue) (ready : value.Ready active) (within : offset+8*value.words≤248)
    (normal : evaluateHOLFiniteState source (storeProgram offset value)=(none,target)) : BeforeMemory source target header := by
  obtain ⟨actual,valueRead,size⟩ := value.read source active state.slots current state.currentCell ready
  have addressRead : eval source (storeAddress offset)=some (.val (.word (header+BitVec.ofNat 64 offset))) := by
    simp [storeAddress,eval,evalHOLExact,evalListHOLExact,toExact,state.headerCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have number : (header+BitVec.ofNat 64 offset).toNat=header.toNat+offset :=
    MemoryBytes.offset_toNat header offset (by have h:=state.headerArena.upper; omega)
  obtain ⟨observed,memory,read,stores,post⟩ := Input.store_at_normal source target (storeAddress offset) value.expression (header+BitVec.ofNat 64 offset) addressRead normal
  have same : observed=actual := Option.some.inj (read.symm.trans valueRead)
  subst observed
  intro query upper
  rw [post]
  apply Input.words_away (flattenHOL actual) (header+BitVec.ofNat 64 offset) query source.memaddrs source.memory memory stores
  intro index inside equal
  have atWord : ((header+BitVec.ofNat 64 offset)+BitVec.ofNat 64 (8*index)).toNat=header.toNat+offset+8*index := by
    rw [MemoryBytes.offset_toNat _ (8*index) (by rw [number]; have h:=state.headerArena.upper; rw [size] at inside; omega),number]
  have same:=congrArg BitVec.toNat equal
  rw [atWord] at same
  omega

end InitECandidate.Solver.Headers.CurrentPipeline

#print axioms InitECandidate.Solver.Headers.CurrentPipeline.State.store_memory
