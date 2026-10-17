import InitECandidate.Solver.Input.VarList.Cells

namespace InitECandidate.Solver.Input.VarList
open Flapjack PanSemStateFiniteExact

/-- Exact pointer-cell effect of the actual iteration state, including that
its optional length write cannot alias any record pointer cell. -/
theorem iteration_pointer_cell (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input)
    (index query : Nat) (small : index<plan.count) (querySmall : query<plan.count) (previous : BitVec 64) :
    (iteration source input plan index previous).memory (row plan.array query)=
      if query=index then .word (plan.inputPointer+BitVec.ofNat 64 plan.start+currentWord input plan.start index) else source.memory (row plan.array query) := by
  classical
  change WitnessRadix.StoreWord.put
    (if 0<index then WitnessRadix.StoreWord.put source.memory (lengthCell plan.array (index-1)) (currentWord input plan.start index-previous) else source.memory)
    (row plan.array index) (plan.inputPointer+BitVec.ofNat 64 plan.start+currentWord input plan.start index) (row plan.array query)=_
  by_cases positive : 0<index
  · simp only [if_pos positive,WitnessRadix.StoreWord.put,plan.row_eq_iff query index querySmall small,
      if_neg (plan.row_ne_length query (index-1) querySmall (by omega))]
  · simp only [if_neg positive,WitnessRadix.StoreWord.put,plan.row_eq_iff query index querySmall small]

/-- Exact length-cell effect: only the immediately preceding record is finished.
The current pointer write cannot alias any length cell. -/
theorem iteration_length_cell (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (plan : Plan input)
    (index query : Nat) (small : index<plan.count) (querySmall : query<plan.count) (previous : BitVec 64) :
    (iteration source input plan index previous).memory (lengthCell plan.array query)=
      if 0<index ∧ query+1=index then .word (currentWord input plan.start index-previous) else source.memory (lengthCell plan.array query) := by
  classical
  change WitnessRadix.StoreWord.put
    (if 0<index then WitnessRadix.StoreWord.put source.memory (lengthCell plan.array (index-1)) (currentWord input plan.start index-previous) else source.memory)
    (row plan.array index) (plan.inputPointer+BitVec.ofNat 64 plan.start+currentWord input plan.start index) (lengthCell plan.array query)=_
  by_cases positive : 0<index
  · have same : query=index-1↔query+1=index := by omega
    simp only [if_pos positive,WitnessRadix.StoreWord.put,
      if_neg (Ne.symm (plan.row_ne_length index query small querySmall)),plan.length_eq_iff query (index-1) querySmall (by omega),same,
      positive,true_and,↓reduceIte]
  · simp only [if_neg positive,WitnessRadix.StoreWord.put,
      if_neg (Ne.symm (plan.row_ne_length index query small querySmall)),positive,false_and,↓reduceIte]

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.iteration_pointer_cell
#print axioms InitECandidate.Solver.Input.VarList.iteration_length_cell
