import InitECandidate.Solver.Input.VarList.Return

namespace InitECandidate.Solver.Input.VarList
open Flapjack PanSemStateFiniteExact

/-- Complete actual record array: each pointer and length cell is initialized.
Adjacent offsets determine lengths; the final record ends at the slice length. -/
def Complete (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input) (total : BitVec 64) : Prop :=
  ∀ query,query<plan.count→
    source.memory (row plan.array query)=.word (plan.inputPointer+BitVec.ofNat 64 plan.start+currentWord input plan.start query) ∧
    source.memory (lengthCell plan.array query)=.word
      ((if query+1<plan.count then currentWord input plan.start (query+1) else total)-currentWord input plan.start query)

/-- The final real length store completes the array while preserving every
pointer cell and every earlier completed record length. -/
theorem complete_finished (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input)
    (total previous : BitVec 64) (filled : Filled source input plan plan.count)
    (last : previous=currentWord input plan.start (plan.count-1)) :
    Complete (finished source plan.array plan.count total previous) input plan total := by
  classical
  have lastSmall : plan.count-1<plan.count := by have h:=plan.positive; omega
  intro query small
  constructor
  · have away:=plan.row_ne_length query (plan.count-1) small lastSmall
    simpa only [finished,WitnessRadix.StoreWord.put,if_neg away] using filled.1 query small
  · by_cases more : query+1<plan.count
    · have different : query≠plan.count-1 := by omega
      have away : lengthCell plan.array query≠lengthCell plan.array (plan.count-1) := by
        intro eq
        exact different ((plan.length_eq_iff query (plan.count-1) small lastSmall).mp eq)
      simpa only [finished,WitnessRadix.StoreWord.put,if_neg away,if_pos more] using filled.2 query more
    · have number : query=plan.count-1 := by omega
      rw [if_neg more,number]
      simp only [finished,WitnessRadix.StoreWord.put,if_pos rfl,last,↓reduceIte]

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.complete_finished
