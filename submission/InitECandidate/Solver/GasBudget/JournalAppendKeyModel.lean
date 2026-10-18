import InitECandidate.Solver.GasBudget.JournalAppendKeyNormal
import InitECandidate.Solver.MutableTable.FamilyMemoryFrame

namespace InitECandidate.Solver.GasBudget.Journal.Append
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout

theorem key_earlier (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (cursor : Nat) (query address : BitVec 64)
    (region : MemoryRegion.Valid ⟨cursor, stride kind⟩) (before : address.toNat < cursor) :
    (keyState source kind cursor query).memory address = source.memory address := by
  have bounded := (key_rounding kind).1
  have away := MemoryRegion.copy_away ⟨cursor, stride kind⟩ region (KeyHash.keySize kind) bounded address (Or.inl before)
  exact CopyGeneral.resultMemory_away source.memory source.be query (BitVec.ofNat 64 cursor) address (KeyHash.keySize kind) away

/-- The actual fresh copied key is beyond every old table. Allocation and
copy preserve all current physical models and the whole journal image. -/
theorem key_models {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (cursor : Nat) (query : BitVec 64)
    (objects : ι → TableFamily.Object) (family : TableFamily.Model source cursor objects)
    (region : MemoryRegion.Valid ⟨cursor, stride kind⟩) :
    TableFamily.Model (keyState source kind cursor query) (cursor + stride kind) objects := by
  have nextBound := region.upper
  change cursor + stride kind ≤ 33806089496 at nextBound
  have aligned := region.aligned
  change cursor % 8 = 0 at aligned
  have nextAligned : (cursor + stride kind) % 8 = 0 := by rw [Nat.add_mod, aligned, (key_rounding kind).2.2.1]
  have heap : (allocated source kind cursor).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + stride kind)))) := by
    simp [allocated, PersistentAlloc.nextState, WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have allocatedFamily : TableFamily.Model (allocated source kind cursor) (cursor + stride kind) objects :=
    family.advance_cursor heap (by omega) nextBound nextAligned rfl rfl rfl
  apply allocatedFamily.of_earlier_words (target := keyState source kind cursor query) (cut := cursor) rfl rfl rfl (fun index => (family.tables index).earlier)
  intro address before
  exact key_earlier source kind cursor query address region before

theorem key_image {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (cursor : Nat) (query : BitVec 64)
    (objects : ι → TableFamily.Object) (base count : Nat) (entries : Nat → Entry ι)
    (image : Image source objects base count entries) (region : MemoryRegion.Valid ⟨cursor, stride kind⟩)
    (extent : base + 32 * count ≤ cursor) : Image (keyState source kind cursor query) objects base count entries := by
  have bounded := region.upper
  change cursor + stride kind ≤ 33806089496 at bounded
  apply image.transfer (target := keyState source kind cursor query) rfl (fun _ => rfl) (fun _ => rfl) _ image.separate
  intro index inside field
  exact key_earlier source kind cursor query _ region (entry_before base count cursor index field extent (by omega) inside)

theorem key_globals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (cursor : Nat) (query : BitVec 64) :
    HeapGlobals source (keyState source kind cursor query) := HeapGlobals.update source _

theorem key_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (cursor : Nat) (query : BitVec 64) :
    (keyState source kind cursor query).clock = source.clock - keyPrice kind cursor query := by
  change source.clock - 1 - (CopyGeneral.cost query (BitVec.ofNat 64 cursor) (KeyHash.keySize kind) + 1) =
    source.clock - (CopyGeneral.cost query (BitVec.ofNat 64 cursor) (KeyHash.keySize kind) + 2)
  omega

end InitECandidate.Solver.GasBudget.Journal.Append

#print axioms InitECandidate.Solver.GasBudget.Journal.Append.key_earlier
#print axioms InitECandidate.Solver.GasBudget.Journal.Append.key_models
#print axioms InitECandidate.Solver.GasBudget.Journal.Append.key_image
#print axioms InitECandidate.Solver.GasBudget.Journal.Append.key_globals
#print axioms InitECandidate.Solver.GasBudget.Journal.Append.key_clock
