import InitECandidate.Solver.Headers.Slots

namespace InitECandidate.Solver.Headers
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

inductive StoreValue where
  | saved (slot : Slot)
  | part (slot : Slot) (index : Nat)
  | current
  | zero

def StoreValue.expression : StoreValue→ExpHOL 64
  | .saved slot=>.var .local slot.name
  | .part slot index=>.rfield index (.var .local slot.name)
  | .current=>localVar "is_current"
  | .zero=>.const 0#64
def StoreValue.words : StoreValue→Nat | .saved slot=>slot.words | _=>1
def StoreValue.Ready (active : List Slot) : StoreValue→Prop
  | .saved slot=>slot∈active
  | .part slot index=>slot∈active ∧ slot.words=2 ∧ index<2
  | .current | .zero=>True

private theorem pair_shape (slot : Slot) (two : slot.words=2) : slot.shape=Input.ScalarPair.tupleShape := by
  cases slot <;> simp_all [Slot.words,Slot.shape]

/-- Current checked helper-slot types determine each literal original
header-store value and its exact one/four-word footprint. Pair projections
also derive the actual scalar word, with no future store outcome premise. -/
theorem StoreValue.read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (active : List Slot)
    (slots : Slots source active) (current : BitVec 64)
    (currentCell : source.locals.lookup (ofString "is_current")=some (.val (.word current)))
    (value : StoreValue) (ready : value.Ready active) :
    ∃ actual,eval source value.expression=some actual ∧ (flattenHOL actual).length=value.words := by
  cases value with
  | saved slot=>
    obtain ⟨actual,cell,size⟩ := slots.store_value source active slot ready
    exact ⟨actual,by simp [StoreValue.expression,eval,evalHOLExact,toExact,cell],size⟩
  | part slot index=>
    obtain ⟨actual,cell,shape⟩ := slots slot ready.1
    rw [pair_shape slot ready.2.1] at shape
    obtain ⟨left,right,same⟩ := Input.ScalarPair.of_shape actual shape
    subst actual
    by_cases first : index=0
    · subst index
      exact ⟨.val (.word left),by simp [StoreValue.expression,eval,evalHOLExact,toExact,cell,Input.ScalarPair.tuple],by simp [StoreValue.words,flattenHOL]⟩
    · have second : index=1 := by have h:=ready.2.2; omega
      subst index
      exact ⟨.val (.word right),by simp [StoreValue.expression,eval,evalHOLExact,toExact,cell,Input.ScalarPair.tuple],by simp [StoreValue.words,flattenHOL]⟩
  | current=>
    exact ⟨.val (.word current),by simp [StoreValue.expression,eval,evalHOLExact,localVar,toExact,currentCell],by simp [StoreValue.words,flattenHOL]⟩
  | zero=>exact ⟨.val (.word 0#64),rfl,by simp [StoreValue.words,flattenHOL]⟩

end InitECandidate.Solver.Headers

#print axioms InitECandidate.Solver.Headers.StoreValue.read
