import InitECandidate.Solver.Headers.HelperCall
import InitECandidate.Solver.Input.ScalarPairShape

namespace InitECandidate.Solver.Headers
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

inductive Slot where | f | d | w | tsf | ex | bg
  deriving DecidableEq

def Slot.name : Slot→MlS
  | .f=>ofString "f" | .d=>ofString "d" | .w=>ofString "w"
  | .tsf=>ofString "tsf" | .ex=>ofString "ex" | .bg=>ofString "bg"
def Slot.words : Slot→Nat | .f | .w=>1 | .d=>4 | _=>2
def Slot.shape : Slot→ShapeHOL
  | .f | .w=>.one | .d=>Input.RlpWrite.U256Value.tupleShape | _=>Input.ScalarPair.tupleShape

theorem Slot.name_injective : Function.Injective Slot.name := by
  intro left right
  cases left <;> cases right <;> decide

/-- Only locals whose real declarations/calls have been reached are tracked.
Their values remain arbitrary; actual helper shape checks supply each type. -/
def Slots (source : PanSemStateFiniteExact 64 Guest.HostMemory) (active : List Slot) : Prop :=
  ∀ slot∈active,∃ value,source.locals.lookup slot.name=some value ∧ shapeOfHOLExact value=slot.shape

theorem Slots.empty (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Slots source [] := by simp [Slots]

theorem Slots.of_locals (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (active : List Slot)
    (slots : Slots source active) (same : target.locals=source.locals) : Slots target active := by
  intro slot member
  rw [same]
  exact slots slot member

/-- Installing an actual checked helper return retains all earlier active
slot types, including reassignment to the same original slot shape. -/
theorem Slots.set (source : PanSemStateFiniteExact 64 Guest.HostMemory) (active : List Slot) (slot : Slot) (value : ValueHOL 64)
    (slots : Slots source active) (shape : shapeOfHOLExact value=slot.shape) :
    Slots (setVarHOLFinite slot.name value source) (slot::active) := by
  intro chosen member
  by_cases same : chosen=slot
  · subst chosen
    exact ⟨value,by simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE],shape⟩
  · have inside : chosen∈active := (List.mem_cons.mp member).resolve_left same
    obtain ⟨old,cell,oldShape⟩ := slots chosen inside
    have different : chosen.name≠slot.name := by intro equal; exact same (Slot.name_injective equal)
    exact ⟨old,by simpa [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different,Ne.symm different] using cell,oldShape⟩

/-- Actual slot types bound the flattened store footprint to one, two or
four words, preventing an assumed tuple size in output-header store proofs. -/
theorem Slots.store_value (source : PanSemStateFiniteExact 64 Guest.HostMemory) (active : List Slot) (slot : Slot)
    (slots : Slots source active) (member : slot∈active) :
    ∃ value,source.locals.lookup slot.name=some value ∧ (flattenHOL value).length=slot.words := by
  obtain ⟨value,cell,shape⟩ := slots slot member
  refine ⟨value,cell,?_⟩
  cases slot
  · obtain ⟨word,rfl⟩ := Input.RlpWrite.U256Value.scalar_word value shape
    simp [Input.ScalarPair.tuple,Input.RlpWrite.U256Value.tuple,flattenHOL,Slot.words]
  · obtain ⟨words,rfl⟩ := Input.RlpWrite.U256Value.of_shape value shape
    simp [Input.ScalarPair.tuple,Input.RlpWrite.U256Value.tuple,flattenHOL,Slot.words]
  · obtain ⟨word,rfl⟩ := Input.RlpWrite.U256Value.scalar_word value shape
    simp [Input.ScalarPair.tuple,Input.RlpWrite.U256Value.tuple,flattenHOL,Slot.words]
  · obtain ⟨left,right,rfl⟩ := Input.ScalarPair.of_shape value shape
    simp [Input.ScalarPair.tuple,Input.RlpWrite.U256Value.tuple,flattenHOL,Slot.words]
  · obtain ⟨left,right,rfl⟩ := Input.ScalarPair.of_shape value shape
    simp [Input.ScalarPair.tuple,Input.RlpWrite.U256Value.tuple,flattenHOL,Slot.words]
  · obtain ⟨left,right,rfl⟩ := Input.ScalarPair.of_shape value shape
    simp [Input.ScalarPair.tuple,Input.RlpWrite.U256Value.tuple,flattenHOL,Slot.words]

end InitECandidate.Solver.Headers

#print axioms InitECandidate.Solver.Headers.Slot.name_injective
#print axioms InitECandidate.Solver.Headers.Slots.empty
#print axioms InitECandidate.Solver.Headers.Slots.of_locals
#print axioms InitECandidate.Solver.Headers.Slots.set
#print axioms InitECandidate.Solver.Headers.Slots.store_value
