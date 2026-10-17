import InitECandidate.Solver.MutableTable.Probe

namespace InitECandidate.Solver.MutableTable.Placement

/-- Forward cyclic distance, for indices and homes inside the capacity. -/
def distance (capacity home index : Nat) : Nat:=if home≤index then index-home else capacity-home+index

theorem distance_bound (capacity home index : Nat) (positive : 0<capacity) (homeInside : home<capacity) (inside : index<capacity) :
    distance capacity home index<capacity := by
  unfold distance
  split <;> omega

theorem slot_distance (capacity home index : Nat) (positive : 0<capacity) (homeInside : home<capacity) (inside : index<capacity) :
    Probe.slot capacity home (distance capacity home index)=index := by
  unfold Probe.slot distance
  by_cases ordered : home≤index
  · rw [if_pos ordered]
    have sum : home+(index-home)=index:=by omega
    rw [sum,Nat.mod_eq_of_lt inside]
  · rw [if_neg ordered]
    have sum : home+(capacity-home+index)=capacity+index:=by omega
    rw [sum,Nat.add_mod]
    simp [Nat.mod_eq_of_lt inside]

abbrev Table (Key Value : Type):=Nat→Option (Key×Value)

/-- Every stored key has an occupied path from its own home to its slot. This
is the placement invariant insertion/growth/backward deletion must maintain. -/
def NoGaps {Key Value : Type} (capacity : Nat) (home : Key→Nat) (table : Table Key Value) : Prop:=
  ∀ index<capacity,∀ key value,table index=some (key,value)→
    ∀ step<distance capacity (home key) index,table (Probe.slot capacity (home key) step)≠none

def Represents {Key Value : Type} (capacity : Nat) (table : Table Key Value) (dictionary : Key→Option Value) : Prop:=
  (∀ index<capacity,∀ key value,table index=some (key,value)→dictionary key=some value) ∧
  (∀ key value,dictionary key=some value→∃ index<capacity,table index=some (key,value))

/-- Fuel-bounded first-match search; the actual byte-level loop is connected
separately. A missing entry stops immediately at the first empty slot. -/
def lookupFrom {Key Value : Type} [DecidableEq Key] (table : Table Key Value) (capacity start : Nat) (query : Key) : Nat→Nat→Option (Nat×Value)
  | _,0=>none
  | offset,fuel+1=>
    let index:=Probe.slot capacity start offset
    match table index with
    | none=>none
    | some (key,value)=>if key=query then some (index,value) else lookupFrom table capacity start query (offset+1) fuel

theorem lookup_sound {Key Value : Type} [DecidableEq Key] (table : Table Key Value) (capacity start : Nat) (query : Key)
    (offset fuel index : Nat) (value : Value)
    (result : lookupFrom table capacity start query offset fuel=some (index,value)) : table index=some (query,value) := by
  induction fuel generalizing offset with
  | zero=>simp [lookupFrom] at result
  | succ fuel ih=>
    cases cell : table (Probe.slot capacity start offset) with
    | none=>simp [lookupFrom,cell] at result
    | some entry=>
      obtain ⟨key,stored⟩:=entry
      by_cases same : key=query
      · simp only [lookupFrom,cell,if_pos same,Option.some.injEq,Prod.mk.injEq] at result
        obtain ⟨locationEq,valued⟩:=result
        simpa only [locationEq,valued,same] using cell
      · simp only [lookupFrom,cell,if_neg same] at result
        exact ih (offset+1) result

theorem lookup_index_bound {Key Value : Type} [DecidableEq Key] (table : Table Key Value) (capacity start : Nat) (query : Key)
    (positive : 0<capacity) (offset fuel index : Nat) (value : Value)
    (result : lookupFrom table capacity start query offset fuel=some (index,value)) : index<capacity := by
  induction fuel generalizing offset with
  | zero=>simp [lookupFrom] at result
  | succ fuel ih=>
    cases cell : table (Probe.slot capacity start offset) with
    | none=>simp [lookupFrom,cell] at result
    | some entry=>
      obtain ⟨key,stored⟩:=entry
      by_cases same : key=query
      · simp only [lookupFrom,cell,if_pos same,Option.some.injEq,Prod.mk.injEq] at result
        rw [← result.1]
        exact Nat.mod_lt _ positive
      · simp only [lookupFrom,cell,if_neg same] at result
        exact ih (offset+1) result

/-- A stored query before fuel exhaustion and no earlier empty ensure some
match; earlier duplicate keys may return before the designated stored slot. -/
theorem lookup_exists_before {Key Value : Type} [DecidableEq Key] (table : Table Key Value) (capacity start : Nat) (query : Key)
    (fuel offset hit : Nat) (stored : Value) (lower : offset≤hit) (within : hit<offset+fuel)
    (atHit : table (Probe.slot capacity start hit)=some (query,stored))
    (occupied : ∀ step,offset≤step→step<hit→table (Probe.slot capacity start step)≠none) :
    ∃ index value,lookupFrom table capacity start query offset fuel=some (index,value) := by
  induction fuel generalizing offset with
  | zero=>omega
  | succ fuel ih=>
    cases cell : table (Probe.slot capacity start offset) with
    | none=>
      by_cases atIndex : offset=hit
      · subst offset
        rw [atHit] at cell
        cases cell
      · exact False.elim (occupied offset (Nat.le_refl _) (by omega) cell)
    | some entry=>
      obtain ⟨key,value⟩:=entry
      by_cases same : key=query
      · exact ⟨Probe.slot capacity start offset,value,by simp only [lookupFrom,cell,if_pos same]⟩
      · have before : offset<hit := by
          by_contra outside
          have atIndex : offset=hit:=by omega
          rw [atIndex,atHit] at cell
          have eq:=Option.some.inj cell
          exact same (congrArg Prod.fst eq).symm
        obtain ⟨index,answer,run⟩:=ih (offset+1) (by omega) (by omega) (by
          intro step lower upper
          exact occupied step (by omega) upper)
        exact ⟨index,answer,by simpa only [lookupFrom,cell,if_neg same] using run⟩

/-- First-match lookup equals the represented dictionary under the maintained
placement invariant. No property of the hash family is assumed. -/
theorem lookup_dictionary {Key Value : Type} [DecidableEq Key] (capacity : Nat) (positive : 0<capacity)
    (home : Key→Nat) (homes : ∀ key,home key<capacity) (table : Table Key Value) (dictionary : Key→Option Value)
    (placed : NoGaps capacity home table) (rep : Represents capacity table dictionary) (query : Key) :
    (lookupFrom table capacity (home query) query 0 capacity).map Prod.snd=dictionary query := by
  cases expected : dictionary query with
  | none=>
    cases actual : lookupFrom table capacity (home query) query 0 capacity with
    | none=>rfl
    | some pair=>
      obtain ⟨index,value⟩:=pair
      have cell:=lookup_sound table capacity (home query) query 0 capacity index value actual
      have inside:=lookup_index_bound table capacity (home query) query positive 0 capacity index value actual
      have inconsistent:=rep.1 index inside query value cell
      rw [expected] at inconsistent
      cases inconsistent
  | some value=>
    obtain ⟨index,inside,cell⟩:=rep.2 query value expected
    have hitInside:=distance_bound capacity (home query) index positive (homes query) inside
    have atHit : table (Probe.slot capacity (home query) (distance capacity (home query) index))=some (query,value) := by
      rw [slot_distance capacity (home query) index positive (homes query) inside]
      exact cell
    obtain ⟨found,answer,actual⟩:=lookup_exists_before table capacity (home query) query capacity 0 (distance capacity (home query) index) value
      (Nat.zero_le _) (by omega) atHit (by intro step lower upper;exact placed index inside query value cell step upper)
    have foundCell:=lookup_sound table capacity (home query) query 0 capacity found answer actual
    have foundInside:=lookup_index_bound table capacity (home query) query positive 0 capacity found answer actual
    have same:=rep.1 found foundInside query answer foundCell
    rw [expected] at same
    rw [actual,Option.map_some]
    exact same.symm

end InitECandidate.Solver.MutableTable.Placement

#print axioms InitECandidate.Solver.MutableTable.Placement.distance_bound
#print axioms InitECandidate.Solver.MutableTable.Placement.slot_distance
#print axioms InitECandidate.Solver.MutableTable.Placement.lookup_sound
#print axioms InitECandidate.Solver.MutableTable.Placement.lookup_index_bound
#print axioms InitECandidate.Solver.MutableTable.Placement.lookup_exists_before
#print axioms InitECandidate.Solver.MutableTable.Placement.lookup_dictionary
