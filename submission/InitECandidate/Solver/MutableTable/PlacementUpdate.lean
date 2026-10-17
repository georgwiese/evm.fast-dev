import InitECandidate.Solver.MutableTable.Placement
import InitECandidate.Solver.WitnessRadix.Model

namespace InitECandidate.Solver.MutableTable.Placement

def put {Key Value : Type} (table : Table Key Value) (index : Nat) (key : Key) (value : Value) : Table Key Value:=
  fun query=>if query=index then some (key,value) else table query

def dictionaryPut {Key Value : Type} [DecidableEq Key] (dictionary : Key→Option Value) (key : Key) (value : Value) : Key→Option Value:=
  fun query=>if query=key then some value else dictionary query

def UniqueKeys {Key Value : Type} (capacity : Nat) (table : Table Key Value) : Prop:=
  ∀ first<capacity,∀ second<capacity,∀ key a b,table first=some (key,a)→table second=some (key,b)→first=second

theorem put_preserves_occupied {Key Value : Type} (table : Table Key Value) (index query : Nat) (key : Key) (value : Value)
    (occupied : table query≠none) : put table index key value query≠none := by
  by_cases same : query=index <;> simp [put,same,occupied]

/-- Insertion at an occupied-path slot, or update at an existing slot,
preserves the no-gap invariant. Runtime writes are not represented here. -/
theorem put_no_gaps {Key Value : Type} (capacity : Nat) (home : Key→Nat) (table : Table Key Value)
    (placed : NoGaps capacity home table) (index : Nat) (key : Key) (value : Value)
    (path : ∀ step<distance capacity (home key) index,table (Probe.slot capacity (home key) step)≠none) :
    NoGaps capacity home (put table index key value) := by
  intro query inside storedKey storedValue cell step before
  by_cases same : query=index
  · subst query
    simp only [put,if_pos rfl,Option.some.injEq,Prod.mk.injEq] at cell
    obtain ⟨rfl,rfl⟩:=cell
    exact put_preserves_occupied table index _ key value (path step before)
  · simp only [put,if_neg same] at cell
    exact put_preserves_occupied table index _ key value (placed query inside storedKey storedValue cell step before)

/-- A safe existing-key update or absent-key insertion implements functional
dictionary overwrite. Unique-key search supplies the chosen-slot premises. -/
theorem put_represents {Key Value : Type} [DecidableEq Key] (capacity : Nat) (table : Table Key Value)
    (dictionary : Key→Option Value) (rep : Represents capacity table dictionary)
    (index : Nat) (inside : index<capacity) (key : Key) (value : Value)
    (chosen : table index=none ∨ ∃ old,table index=some (key,old))
    (only : ∀ query<capacity,∀ old,table query=some (key,old)→query=index) :
    Represents capacity (put table index key value) (dictionaryPut dictionary key value) := by
  constructor
  · intro query queryInside storedKey storedValue cell
    by_cases atIndex : query=index
    · subst query
      simp only [put,if_pos rfl,Option.some.injEq,Prod.mk.injEq] at cell
      obtain ⟨rfl,rfl⟩:=cell
      simp [dictionaryPut]
    · simp only [put,if_neg atIndex] at cell
      by_cases same : storedKey=key
      · subst storedKey
        exact False.elim (atIndex (only query queryInside storedValue cell))
      · simpa only [dictionaryPut,if_neg same] using rep.1 query queryInside storedKey storedValue cell
  · intro query answer updated
    by_cases same : query=key
    · subst query
      simp only [dictionaryPut,if_pos rfl,ite_true,Option.some.injEq] at updated
      exact ⟨index,inside,by simp [put,updated]⟩
    · simp only [dictionaryPut,if_neg same] at updated
      obtain ⟨slot,slotInside,cell⟩:=rep.2 query answer updated
      have away : slot≠index := by
        intro equal
        subst slot
        rcases chosen with empty|⟨old,stored⟩
        · rw [empty] at cell;cases cell
        · rw [stored] at cell
          have pairEq:=Option.some.inj cell
          exact same (congrArg Prod.fst pairEq).symm
      exact ⟨slot,slotInside,by simpa only [put,if_neg away] using cell⟩

theorem put_unique {Key Value : Type} (capacity : Nat) (table : Table Key Value)
    (unique : UniqueKeys capacity table) (index : Nat) (key : Key) (value : Value)
    (only : ∀ query<capacity,∀ old,table query=some (key,old)→query=index) :
    UniqueKeys capacity (put table index key value) := by
  intro first firstInside second secondInside storedKey a b firstCell secondCell
  by_cases atFirst : first=index
  · subst first
    simp only [put,if_pos rfl,Option.some.injEq,Prod.mk.injEq] at firstCell
    obtain ⟨rfl,rfl⟩:=firstCell
    by_cases atSecond : second=index
    · exact atSecond.symm
    · simp only [put,if_neg atSecond] at secondCell
      exact (only second secondInside b secondCell).symm
  · simp only [put,if_neg atFirst] at firstCell
    by_cases atSecond : second=index
    · subst second
      simp only [put,if_pos rfl,Option.some.injEq,Prod.mk.injEq] at secondCell
      obtain ⟨rfl,rfl⟩:=secondCell
      exact only first firstInside a firstCell
    · simp only [put,if_neg atSecond] at secondCell
      exact unique first firstInside second secondInside storedKey a b firstCell secondCell

theorem empty_invariants {Key Value : Type} (capacity : Nat) (home : Key→Nat) :
    NoGaps capacity home (fun _=>none : Table Key Value) ∧
      Represents capacity (fun _=>none : Table Key Value) (fun _=>none) ∧ UniqueKeys capacity (fun _=>none : Table Key Value) := by
  constructor
  · intro index inside key value cell;cases cell
  · constructor
    · constructor
      · intro index inside key value cell;cases cell
      · intro key value cell;cases cell
    · intro first firstInside second secondInside key a b firstCell;cases firstCell

/-- The abstract overwrite is the same last-record-wins dictionary used by
the checked radix model, including all duplicates and absent keys. -/
theorem overwrite_lastValue {Key Value : Type} [DecidableEq Key] (input : List (Key×Value)) (key : Key) (value : Value) (query : Key) :
    dictionaryPut (fun q=>WitnessRadix.lastValue q input) key value query=WitnessRadix.lastValue query (input++[(key,value)]) := by
  induction input with
  | nil=>by_cases same : query=key <;> simp [dictionaryPut,WitnessRadix.lastValue,same,Ne.symm]
  | cons head rest ih=>
    by_cases same : query=key
    · subst query
      simp only [dictionaryPut,if_pos rfl,ite_true] at ih ⊢
      simp only [List.cons_append,WitnessRadix.lastValue,← ih]
    · simp only [dictionaryPut,if_neg same] at ih ⊢
      simp only [List.cons_append,WitnessRadix.lastValue,← ih]

end InitECandidate.Solver.MutableTable.Placement

#print axioms InitECandidate.Solver.MutableTable.Placement.put_preserves_occupied
#print axioms InitECandidate.Solver.MutableTable.Placement.put_no_gaps
#print axioms InitECandidate.Solver.MutableTable.Placement.put_represents
#print axioms InitECandidate.Solver.MutableTable.Placement.put_unique
#print axioms InitECandidate.Solver.MutableTable.Placement.empty_invariants
#print axioms InitECandidate.Solver.MutableTable.Placement.overwrite_lastValue
