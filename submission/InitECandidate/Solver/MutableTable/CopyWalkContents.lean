import InitECandidate.Solver.MutableTable.CopyStageContents

namespace InitECandidate.Solver.MutableTable.TableCopy
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

theorem walk_other_data (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old next : Plan)
    (nextValid : Valid kind next) (sameCapacity : next.capacity = old.capacity) (selected : List Pool)
    (other : Pool) (absent : other ∉ selected) (notHeader : other ≠ .header) (query : Nat) (inside : query < size kind next other) :
    (walk source kind old next selected).memory (cell next other query) = source.memory (cell next other query) := by
  induction selected generalizing source with
  | nil => rfl
  | cons pool rest ih =>
    have different : other ≠ pool := by intro same; exact absent (by simp [same])
    have notLater : other ∉ rest := by intro member; exact absent (List.mem_cons_of_mem _ member)
    rw [walk, ih _ notLater, stage_memory]
    exact stage_other_data _ _ kind old next nextValid sameCapacity pool other different notHeader query inside

theorem walk_other_byte (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old next : Plan)
    (nextValid : Valid kind next) (sameCapacity : next.capacity = old.capacity) (selected : List Pool)
    (other : Pool) (absent : other ∉ selected) (notHeader : other ≠ .header) (query : Nat) (inside : query < size kind next other) :
    CopyContents.byte (walk source kind old next selected).memory (cell next other query) = CopyContents.byte source.memory (cell next other query) := by
  unfold CopyContents.byte
  rw [byte_cell kind next nextValid other query inside,
    walk_other_data source kind old next nextValid sameCapacity selected other absent notHeader _ (by omega)]

theorem stage_old_byte (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old next : Plan)
    (oldValid : Valid kind old) (nextValid : Valid kind next) (sameCapacity : next.capacity = old.capacity)
    (earlier : ∀ first second, old.base first + size kind old first ≤ next.base second)
    (pool other : Pool) (query : Nat) (inside : query < size kind old other) :
    CopyContents.byte (stageState source kind old next pool).memory (cell old other query) = CopyContents.byte source.memory (cell old other query) := by
  unfold CopyContents.byte
  rw [byte_cell kind old oldValid other query inside, stage_memory]
  rw [stage_preserves_old source.memory source.be kind old next oldValid nextValid sameCapacity earlier pool other _ (by omega)]

theorem walk_word_at (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old next : Plan)
    (oldValid : Valid kind old) (nextValid : Valid kind next) (sameCapacity : next.capacity = old.capacity)
    (earlier : ∀ first second, old.base first + size kind old first ≤ next.base second)
    (selected : List Pool) (other : Pool) (member : other ∈ selected) (notHeader : other ≠ .header) (notUsed : other ≠ .used)
    (query : Nat) (inside : query < size kind old other) (aligned : query % 8 = 0) :
    (walk source kind old next selected).memory (cell next other query) = source.memory (cell old other query) := by
  induction selected generalizing source with
  | nil => cases member
  | cons pool rest ih =>
    by_cases later : other ∈ rest
    · rw [walk, ih _ later, stage_memory]
      exact stage_preserves_old source.memory source.be kind old next oldValid nextValid sameCapacity earlier pool other query inside
    · have equal : other = pool := (List.mem_cons.mp member).resolve_right later
      subst pool
      rw [walk, walk_other_data _ kind old next nextValid sameCapacity rest other later notHeader query (by rw [same_sizes kind old next sameCapacity]; exact inside), stage_memory]
      exact stage_word_at source.memory source.be kind old next oldValid nextValid sameCapacity earlier other notUsed query inside aligned

theorem walk_used_at (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old next : Plan)
    (oldValid : Valid kind old) (nextValid : Valid kind next) (sameCapacity : next.capacity = old.capacity)
    (earlier : ∀ first second, old.base first + size kind old first ≤ next.base second)
    (shape : old.capacity = 4 ∨ old.capacity % 8 = 0) (little : source.be = false)
    (selected : List Pool) (member : Pool.used ∈ selected) (query : Nat) (inside : query < old.capacity) :
    CopyContents.byte (walk source kind old next selected).memory (cell next .used query) = CopyContents.byte source.memory (cell old .used query) := by
  induction selected generalizing source with
  | nil => cases member
  | cons pool rest ih =>
    by_cases later : Pool.used ∈ rest
    · have keptEndian := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.be) (stage_frame source kind old next pool)
      rw [walk, ih (stageState source kind old next pool) (keptEndian.trans little) later]
      exact stage_old_byte source kind old next oldValid nextValid sameCapacity earlier pool .used query (used_offset_inside kind old query inside)
    · have equal : Pool.used = pool := (List.mem_cons.mp member).resolve_right later
      subst pool
      rw [walk, walk_other_byte _ kind old next nextValid sameCapacity rest .used later (by decide) query (by rw [same_sizes kind old next sameCapacity]; exact used_offset_inside kind old query inside), stage_memory, little]
      exact stage_used_at source.memory kind old next oldValid nextValid sameCapacity earlier shape query inside

def headerWord (original : HolWordLab 64) (next : Plan) (query : Nat) : List Pool → HolWordLab 64
  | [] => original
  | pool :: rest => headerWord (if query = headerOffset pool then .word (cell next pool 0) else original) next query rest

theorem walk_header_at (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old next : Plan)
    (nextValid : Valid kind next) (sameCapacity : next.capacity = old.capacity) (selected : List Pool)
    (noHeader : Pool.header ∉ selected) (query : Nat) (inside : query < 72) :
    (walk source kind old next selected).memory (cell next .header query) = headerWord (source.memory (cell next .header query)) next query selected := by
  induction selected generalizing source with
  | nil => rfl
  | cons pool rest ih =>
    have different : pool ≠ .header := by intro same; exact noHeader (by simp [same])
    have absent : Pool.header ∉ rest := by intro member; exact noHeader (List.mem_cons_of_mem _ member)
    rw [walk, ih _ absent, stage_memory, stage_header_at _ _ kind old next nextValid sameCapacity pool different query inside]
    rfl

end InitECandidate.Solver.MutableTable.TableCopy

#print axioms InitECandidate.Solver.MutableTable.TableCopy.walk_other_data
#print axioms InitECandidate.Solver.MutableTable.TableCopy.walk_other_byte
#print axioms InitECandidate.Solver.MutableTable.TableCopy.stage_old_byte
#print axioms InitECandidate.Solver.MutableTable.TableCopy.walk_word_at
#print axioms InitECandidate.Solver.MutableTable.TableCopy.walk_used_at
#print axioms InitECandidate.Solver.MutableTable.TableCopy.walk_header_at
