import InitECandidate.Solver.WitnessRadix.Model

namespace InitECandidate.Solver.MutableTable.DictionaryData
open WitnessRadix

theorem lastValue_member {Key Value : Type} [DecidableEq Key] (query : Key) (input : List (Key×Value))
    (value : Value) (found : lastValue query input=some value) : (query,value)∈input := by
  induction input generalizing value with
  | nil=>simp [lastValue] at found
  | cons entry rest ih=>
    cases tail : lastValue query rest with
    | none=>
      by_cases same : entry.1=query
      · have valueEq : entry.2=value:=by simpa only [lastValue,tail,if_pos same,Option.some.injEq] using found
        exact List.mem_cons.mpr (Or.inl (Prod.ext same.symm valueEq.symm))
      · simp [lastValue,tail,same] at found
    | some previous=>
      have valueEq : previous=value:=by simpa only [lastValue,tail,Option.some.injEq] using found
      subst value
      exact List.mem_cons_of_mem entry (ih previous tail)

theorem lastValue_map {Key Value Target : Type} [DecidableEq Key] (query : Key) (input : List (Key×Value)) (f : Value→Target) :
    (lastValue query input).map f=lastValue query (input.map (fun entry=>(entry.1,f entry.2))) := by
  induction input with
  | nil=>rfl
  | cons entry rest ih=>
    simp only [List.map_cons,lastValue]
    rw [← ih]
    cases tail : lastValue query rest with
    | none=>by_cases same : entry.1=query <;> simp [same]
    | some value=>rfl

end InitECandidate.Solver.MutableTable.DictionaryData

#print axioms InitECandidate.Solver.MutableTable.DictionaryData.lastValue_member
#print axioms InitECandidate.Solver.MutableTable.DictionaryData.lastValue_map
