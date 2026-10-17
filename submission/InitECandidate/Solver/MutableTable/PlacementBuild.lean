import InitECandidate.Solver.MutableTable.PlacementUpdate

namespace InitECandidate.Solver.MutableTable.Placement

/-- A fixed-capacity insertion/update trace. Chosen-slot premises are the
logical properties the actual no-growth setter must establish. -/
inductive Builds {Key Value : Type} (capacity : Nat) (home : Key→Nat) : List (Key×Value)→Table Key Value→Prop where
  | empty : Builds capacity home [] (fun _=>none)
  | snoc (input : List (Key×Value)) (table : Table Key Value) (prior : Builds capacity home input table)
      (index : Nat) (key : Key) (value : Value) (inside : index<capacity)
      (chosen : table index=none ∨ ∃ old,table index=some (key,old))
      (only : ∀ query<capacity,∀ old,table query=some (key,old)→query=index)
      (path : ∀ step<distance capacity (home key) index,table (Probe.slot capacity (home key) step)≠none) :
      Builds capacity home (input++[(key,value)]) (put table index key value)

/-- Original linear-table insertion/update semantics has exactly the same
last-record-wins dictionary as radix construction, under its placement trace. -/
theorem build_invariants {Key Value : Type} [DecidableEq Key] (capacity : Nat) (home : Key→Nat)
    (input : List (Key×Value)) (table : Table Key Value) (trace : Builds capacity home input table) :
    NoGaps capacity home table ∧ Represents capacity table (fun key=>WitnessRadix.lastValue key input) ∧ UniqueKeys capacity table := by
  induction trace with
  | empty=>exact empty_invariants capacity home
  | snoc input table prior index key value inside chosen only path ih=>
    refine ⟨put_no_gaps capacity home table ih.1 index key value path,?_,put_unique capacity table ih.2.2 index key value only⟩
    have updated:=put_represents capacity table (fun q=>WitnessRadix.lastValue q input) ih.2.1 index inside key value chosen only
    have dictionaryEq : dictionaryPut (fun q=>WitnessRadix.lastValue q input) key value=
        (fun q=>WitnessRadix.lastValue q (input++[(key,value)])) := by
      funext query
      exact overwrite_lastValue input key value query
    rw [dictionaryEq] at updated
    exact updated

/-- An insertion history itself covers all occupied slots using at most one
slot per input record. An order-array correspondence is unnecessary for this
counting witness; runtime physical-table correspondence is still required. -/
theorem build_cover {Key Value : Type} (capacity : Nat) (home : Key→Nat)
    (input : List (Key×Value)) (table : Table Key Value) (trace : Builds capacity home input table) :
    ∃ order : List Nat,order.length≤input.length ∧ ∀ index<capacity,table index≠none→index∈order := by
  induction trace with
  | empty=>exact ⟨[],Nat.le_refl _,by intro index inside occupied;exact False.elim (occupied rfl)⟩
  | snoc input table prior index key value inside chosen only path ih=>
    obtain ⟨order,bound,covered⟩:=ih
    refine ⟨order++[index],by simpa only [List.length_append,List.length_singleton] using Nat.add_le_add_right bound 1,?_⟩
    intro query queryInside occupied
    by_cases atIndex : query=index
    · simp [atIndex]
    · simp only [put,if_neg atIndex] at occupied
      exact List.mem_append_left _ (covered query queryInside occupied)

theorem build_lookup {Key Value : Type} [DecidableEq Key] (capacity : Nat) (positive : 0<capacity) (home : Key→Nat)
    (homes : ∀ key,home key<capacity) (input : List (Key×Value)) (table : Table Key Value)
    (trace : Builds capacity home input table) (query : Key) :
    (lookupFrom table capacity (home query) query 0 capacity).map Prod.snd=WitnessRadix.lastValue query input := by
  have invariants:=build_invariants capacity home input table trace
  exact lookup_dictionary capacity positive home homes table _ invariants.1 invariants.2.1 query

/-- Abstract original-table/radix agreement for every key, including duplicates
and absent queries. It is not yet a refinement of the actual mutating code. -/
theorem build_radix_agreement {Key Value : Type} [DecidableEq Key] (capacity : Nat) (positive : 0<capacity) (home : Key→Nat)
    (homes : ∀ key,home key<capacity) (input : List (Key×Value)) (table : Table Key Value)
    (trace : Builds capacity home input table) (bit : Key→Nat→Bool) (position fuel : Nat) (query : Key) :
    (lookupFrom table capacity (home query) query 0 capacity).map Prod.snd=
      WitnessRadix.lookup bit query (WitnessRadix.build bit position fuel input) := by
  rw [build_lookup capacity positive home homes input table trace query,WitnessRadix.lookup_build]

end InitECandidate.Solver.MutableTable.Placement

#print axioms InitECandidate.Solver.MutableTable.Placement.build_invariants
#print axioms InitECandidate.Solver.MutableTable.Placement.build_cover
#print axioms InitECandidate.Solver.MutableTable.Placement.build_lookup
#print axioms InitECandidate.Solver.MutableTable.Placement.build_radix_agreement
