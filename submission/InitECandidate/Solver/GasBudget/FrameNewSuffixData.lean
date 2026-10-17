import InitECandidate.Solver.GasBudget.FrameNewCounts
import InitECandidate.Solver.Arenas.Region
import InitECandidate.Solver.Arenas.Program

namespace InitECandidate.Solver.GasBudget.FrameNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure SuffixWords where
  code : BitVec 64
  length : BitVec 64
  addresses : BitVec 64
  keys : BitVec 64
  addressCount : BitVec 64
  keyCount : BitVec 64

def suffixCells (message : BitVec 64) (words : SuffixWords) : List (BitVec 64 × BitVec 64) :=
  [(message + 112#64, words.code), (message + 120#64, words.length),
   (message + 152#64, words.addresses), (message + 160#64, words.keys),
   (words.addresses + 24#64, words.addressCount), (words.keys + 24#64, words.keyCount)]

/-- Only the constructor's actual external reads and its allocated frame slots.
Neither helper results nor successful execution are fields of this predicate. -/
structure SuffixReady (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame message : BitVec 64) (words : SuffixWords) (empty : BitVec 64) : Prop where
  frameLocal : source.locals.lookup (ofString "e") = some (.val (.word frame))
  messageLocal : source.locals.lookup (ofString "msg") = some (.val (.word message))
  emptyGlobal : source.globals.lookup (ofString "evm_empty") = some (.val (.word empty))
  readsMapped : ∀ cell ∈ suffixCells message words, source.memaddrs cell.1
  readsStored : ∀ cell ∈ suffixCells message words, source.memory cell.1 = .word cell.2
  frameMapped : ∀ offset, offset + 8 ≤ 280 → offset % 8 = 0 → source.memaddrs (frame + BitVec.ofNat 64 offset)

namespace SuffixReady
variable {source : PanSemStateFiniteExact 64 Guest.HostMemory} {frame message : BitVec 64}
  {words : SuffixWords} {empty : BitVec 64}

theorem clock (ready : SuffixReady source frame message words empty) (nextClock : Nat) :
    SuffixReady {source with clock := nextClock} frame message words empty :=
  ⟨ready.frameLocal, ready.messageLocal, ready.emptyGlobal, ready.readsMapped, ready.readsStored, ready.frameMapped⟩

theorem memory (ready : SuffixReady source frame message words empty) (nextMemory : Memory)
    (kept : ∀ cell ∈ suffixCells message words, nextMemory cell.1 = source.memory cell.1) :
    SuffixReady {source with memory := nextMemory} frame message words empty :=
  ⟨ready.frameLocal, ready.messageLocal, ready.emptyGlobal, ready.readsMapped,
    by intro cell member; exact (kept cell member).trans (ready.readsStored cell member), ready.frameMapped⟩

theorem scratch (ready : SuffixReady source frame message words empty) (cursor : BitVec 64) :
    SuffixReady {source with globals := source.globals.update (ofString "scratch_ptr", .val (.word cursor))}
      frame message words empty := by
  refine ⟨ready.frameLocal, ready.messageLocal, ?_, ready.readsMapped, ready.readsStored, ready.frameMapped⟩
  simpa [HolFiniteMapExact.update, FUPDATE, ofString] using ready.emptyGlobal

theorem bound (ready : SuffixReady source frame message words empty) (name : String) (word : BitVec 64)
    (notFrame : ofString name ≠ ofString "e") (notMessage : ofString name ≠ ofString "msg") :
    SuffixReady (WitnessRadix.QueryBranch.bind source name word) frame message words empty :=
  ⟨(bind_lookup_other _ name "e" _ notFrame).trans ready.frameLocal,
   (bind_lookup_other _ name "msg" _ notMessage).trans ready.messageLocal,
   ready.emptyGlobal, ready.readsMapped, ready.readsStored, ready.frameMapped⟩

/-- A memory-only frame transports every actual constructor input word. -/
theorem stored (ready : SuffixReady source frame message words empty) (fields : List FieldStores.Field)
    (away : ∀ cell ∈ suffixCells message words, cell.1 ∉ (FieldStores.writes frame fields).map Prod.fst) :
    SuffixReady {source with memory := WitnessRadix.WordWrites.write source.memory (FieldStores.writes frame fields)}
      frame message words empty :=
  ready.memory _ (by intro cell member; exact WitnessRadix.WordWrites.write_away _ _ _ (away cell member))

theorem copied (ready : SuffixReady source frame message words empty) (offset : Nat) (word : BitVec 64)
    (member : (message + BitVec.ofNat 64 offset, word) ∈ suffixCells message words) :
    FieldStores.Value.Ready source "msg" message (.copied offset word) :=
  ⟨ready.messageLocal, ready.readsMapped _ member, ready.readsStored _ member⟩

end SuffixReady

/-- External input words lie in persistent/earlier allocated memory, separated
from this new frame and the descending scratch allocations. -/
def SuffixProtected (lower frame : BitVec 64) (query : BitVec 64) : Prop :=
  query.toNat < lower.toNat ∨ frame.toNat + 280 ≤ query.toNat

theorem suffix_protected_outside (lower frame cursor query : BitVec 64)
    (protectedRead : SuffixProtected lower frame query) (above : cursor.toNat ≤ frame.toNat) :
    Arenas.Outside lower cursor query := by
  rcases protectedRead with below | high
  · exact Or.inl below
  · exact Or.inr (by omega)

theorem suffix_protected_away (lower frame query : BitVec 64) (offset : Nat)
    (protectedRead : SuffixProtected lower frame query) (lowerOrder : lower.toNat ≤ frame.toNat)
    (frameFits : frame.toNat + 280 < 2 ^ 64) (inside : offset < 280) :
    query ≠ frame + BitVec.ofNat 64 offset := by
  have offsetNumber : (BitVec.ofNat 64 offset).toNat = offset := by
    change offset % 2 ^ 64 = offset
    exact Nat.mod_eq_of_lt (by omega)
  have addressNumber : (frame + BitVec.ofNat 64 offset).toNat = frame.toNat + offset := by
    rw [BitVec.toNat_add_of_lt (by rw [offsetNumber]; omega), offsetNumber]
  intro same
  have number := congrArg BitVec.toNat same
  rw [addressNumber] at number
  rcases protectedRead with below | high <;> omega


def suffixStoreOffsets : List Nat := [80, 88, 104, 112, 136, 168, 176, 264, 272, 120, 144, 216]

def SuffixSafe (lower frame query : BitVec 64) : Prop :=
  (query.toNat < lower.toNat ∨ frame.toNat ≤ query.toNat) ∧
    ∀ offset ∈ suffixStoreOffsets, query ≠ frame + BitVec.ofNat 64 offset

theorem suffix_safe_outside (lower frame cursor query : BitVec 64)
    (safe : SuffixSafe lower frame query) (above : cursor.toNat ≤ frame.toNat) :
    Arenas.Outside lower cursor query := by
  rcases safe.1 with below | high
  · exact Or.inl below
  · exact Or.inr (by omega)

theorem suffix_protected_safe (lower frame query : BitVec 64)
    (protectedRead : SuffixProtected lower frame query) (lowerOrder : lower.toNat ≤ frame.toNat)
    (frameFits : frame.toNat + 280 < 2 ^ 64) : SuffixSafe lower frame query := by
  refine ⟨?_, ?_⟩
  · rcases protectedRead with below | high
    · exact Or.inl below
    · exact Or.inr (by omega)
  · intro offset member
    apply suffix_protected_away lower frame query offset protectedRead lowerOrder frameFits
    simp only [suffixStoreOffsets, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem suffix_regular_safe (lower frame : BitVec 64) (offset : Nat)
    (member : offset ∈ ([64, 184, 192] : List Nat)) (frameFits : frame.toNat + 280 < 2 ^ 64) :
    SuffixSafe lower frame (frame + BitVec.ofNat 64 offset) := by
  refine ⟨Or.inr ?_, ?_⟩
  · have offsetSmall : offset < 280 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl | rfl <;> decide
    have offsetNumber : (BitVec.ofNat 64 offset).toNat = offset := by
      change offset % 2 ^ 64 = offset
      exact Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_add_of_lt (by rw [offsetNumber]; omega), offsetNumber]
    omega
  · intro other otherIn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    simp only [suffixStoreOffsets, List.mem_cons, List.not_mem_nil, or_false] at otherIn
    rcases member with rfl | rfl | rfl <;>
      rcases otherIn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [BitVec.add_right_inj]

end InitECandidate.Solver.GasBudget.FrameNew

#print axioms InitECandidate.Solver.GasBudget.FrameNew.SuffixReady.clock
#print axioms InitECandidate.Solver.GasBudget.FrameNew.SuffixReady.memory
#print axioms InitECandidate.Solver.GasBudget.FrameNew.SuffixReady.scratch
#print axioms InitECandidate.Solver.GasBudget.FrameNew.SuffixReady.bound
#print axioms InitECandidate.Solver.GasBudget.FrameNew.SuffixReady.stored
#print axioms InitECandidate.Solver.GasBudget.FrameNew.SuffixReady.copied
#print axioms InitECandidate.Solver.GasBudget.FrameNew.suffix_protected_outside
#print axioms InitECandidate.Solver.GasBudget.FrameNew.suffix_protected_away

#print axioms InitECandidate.Solver.GasBudget.FrameNew.suffix_safe_outside
#print axioms InitECandidate.Solver.GasBudget.FrameNew.suffix_protected_safe
#print axioms InitECandidate.Solver.GasBudget.FrameNew.suffix_regular_safe
