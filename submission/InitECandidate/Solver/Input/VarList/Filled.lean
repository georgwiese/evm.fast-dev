import InitECandidate.Solver.Input.VarList.IterationMemory

namespace InitECandidate.Solver.Input.VarList
open Flapjack PanSemStateFiniteExact

/-- Initialized record pointers and all lengths except the pending final one.
This assertion describes actual memory cells, without assuming valid offsets. -/
def Filled (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input) (index : Nat) : Prop :=
  (∀ query,query<index→source.memory (row plan.array query)=.word (plan.inputPointer+BitVec.ofNat 64 plan.start+currentWord input plan.start query)) ∧
  (∀ query,query+1<index→source.memory (lengthCell plan.array query)=.word (currentWord input plan.start (query+1)-currentWord input plan.start query))

theorem filled_zero (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input) :
    Filled source input plan 0 := by
  constructor <;> intro query impossible <;> omega

/-- One exact iteration initializes its pointer, finishes the previous length
and preserves all earlier initialized cells. -/
theorem filled_iteration (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input)
    (index : Nat) (small : index<plan.count) (previous : BitVec 64) (filled : Filled source input plan index)
    (previousIndex : 0<index→previous=currentWord input plan.start (index-1)) :
    Filled (iteration source input plan index previous) input plan (index+1) := by
  constructor
  · intro query inside
    rw [iteration_pointer_cell source input plan index query small (by omega) previous]
    by_cases same : query=index
    · simp only [if_pos same]
      rw [same]
    · simp only [if_neg same]
      exact filled.1 query (by omega)
  · intro query inside
    rw [iteration_length_cell source input plan index query small (by omega) previous]
    by_cases same : query+1=index
    · have positive : 0<index := by omega
      rw [if_pos ⟨positive,same⟩]
      have prevEq : previous=currentWord input plan.start query := by
        have eq:=previousIndex positive
        have number : index-1=query := by omega
        rw [number] at eq
        exact eq
      rw [prevEq,←same]
    · rw [if_neg (show ¬(0<index ∧ query+1=index) from fun h=>same h.2)]
      exact filled.2 query (by omega)

/-- The exact walk initializes every record reached by its real iterations.
Heap and byte facts are established by the execution theorem separately. -/
theorem walk_filled (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input)
    (index rounds : Nat) (inside : index+rounds≤plan.count) (previous : BitVec 64)
    (filled : Filled source input plan index)
    (previousIndex : 0<index→previous=currentWord input plan.start (index-1)) :
    Filled (walk source input plan index previous rounds) input plan (index+rounds) := by
  induction rounds generalizing source index previous with
  | zero=>simpa only [walk,Nat.add_zero] using filled
  | succ rounds ih=>
    have active : index<plan.count := by omega
    have entryFilled : Filled (decClockHOLFinite source) input plan index := filled
    have nextFilled:=filled_iteration (decClockHOLFinite source) input plan index active previous entryFilled previousIndex
    have nextPrevious : 0<index+1→currentWord input plan.start index=currentWord input plan.start (index+1-1) := by intro positive; simp
    have final:=ih (iteration (decClockHOLFinite source) input plan index previous) (index+1) (by omega)
      (currentWord input plan.start index) nextFilled nextPrevious
    have number : index+1+rounds=index+(rounds+1) := by omega
    rw [number] at final
    exact final

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.filled_zero
#print axioms InitECandidate.Solver.Input.VarList.filled_iteration
#print axioms InitECandidate.Solver.Input.VarList.walk_filled
