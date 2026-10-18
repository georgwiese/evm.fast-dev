import InitECandidate.Solver.GasBudget.JournalCounter
import InitECandidate.Solver.MutableTable.MemoryRegion
import InitECandidate.Solver.MutableTable.TableFootprint

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

structure Entry (ι : Type) where
  writer : ι
  key : BitVec 64
  flag : BitVec 64
  value : BitVec 64

def entryWord {ι : Type} (objects : ι → TableFamily.Object) (entry : Entry ι) (field : Fin 4) : BitVec 64 :=
  match field.val with
  | 0 => (objects entry.writer).pointer
  | 1 => entry.key
  | 2 => entry.flag
  | _ => entry.value

def entryAddress (base index : Nat) (field : Fin 4) : BitVec 64 := BitVec.ofNat 64 (base + 32 * index + 8 * field.val)

/-- Actual fixed journal words and copied query buffers for the live prefix.
The separation covers tables allocated on either side of the journal. -/
structure Image {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (objects : ι → TableFamily.Object) (base count : Nat) (entries : Nat → Entry ι) : Prop where
  mapped : ∀ index < count, ∀ field, source.memaddrs (entryAddress base index field)
  words : ∀ index < count, ∀ field, source.memory (entryAddress base index field) = .word (entryWord objects (entries index) field)
  separate : ∀ index < count, ∀ field table, TableFootprint.Outside (objects table).kind (objects table).plan (entryAddress base index field)
  queryFits : ∀ index < count, (entries index).key.toNat + KeyHash.keySize (objects (entries index).writer).kind < 2 ^ 64
  queryMapped : ∀ index < count, ∀ offset < KeyHash.keySize (objects (entries index).writer).kind,
    source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress (entries index).key offset))

theorem Image.restrict {ι : Type} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {objects : ι → TableFamily.Object} {base count next : Nat} {entries : Nat → Entry ι}
    (image : Image source objects base count entries) (smaller : next ≤ count) : Image source objects base next entries :=
  ⟨fun index inside => image.mapped index (by omega), fun index inside => image.words index (by omega),
    fun index inside => image.separate index (by omega), fun index inside => image.queryFits index (by omega),
    fun index inside => image.queryMapped index (by omega)⟩

theorem entryWord_of_pointers {ι : Type} (first second : ι → TableFamily.Object)
    (pointers : ∀ index, (second index).pointer = (first index).pointer) (entry : Entry ι) (field : Fin 4) :
    entryWord second entry field = entryWord first entry field := by
  unfold entryWord
  split <;> try rfl
  exact pointers _

/-- An actual mutation carries the remaining journal image using its checked
word frame, stable header pointers and retained query kinds/domain. -/
theorem Image.transfer {ι : Type} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {objects next : ι → TableFamily.Object} {base count : Nat} {entries : Nat → Entry ι}
    (image : Image source objects base count entries)
    (domain : target.memaddrs = source.memaddrs)
    (pointers : ∀ index, (next index).pointer = (objects index).pointer)
    (kinds : ∀ index, (next index).kind = (objects index).kind)
    (words : ∀ index < count, ∀ field, target.memory (entryAddress base index field) = source.memory (entryAddress base index field))
    (separate : ∀ index < count, ∀ field table, TableFootprint.Outside (next table).kind (next table).plan (entryAddress base index field)) :
    Image target next base count entries := by
  constructor
  · intro index inside field
    rw [domain]; exact image.mapped index inside field
  · intro index inside field
    rw [words index inside field, image.words index inside field, entryWord_of_pointers objects next pointers]
  · exact separate
  · intro index inside
    rw [kinds]; exact image.queryFits index inside
  · intro index inside offset bounded
    rw [kinds] at bounded
    rw [domain]; exact image.queryMapped index inside offset bounded

/-- Every word of an earlier complete journal record is below the live
cursor, including its final value word. -/
theorem entry_before (base count cursor index : Nat) (field : Fin 4)
    (extent : base + 32 * count ≤ cursor) (bounded : cursor < 2 ^ 64) (inside : index < count) :
    (entryAddress base index field).toNat < cursor := by
  have fieldBound := field.isLt
  have room : base + 32 * index + 8 * field.val < cursor := by omega
  rw [entryAddress, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact room

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.Image.restrict
#print axioms InitECandidate.Solver.GasBudget.Journal.entryWord_of_pointers
#print axioms InitECandidate.Solver.GasBudget.Journal.Image.transfer
#print axioms InitECandidate.Solver.GasBudget.Journal.entry_before
