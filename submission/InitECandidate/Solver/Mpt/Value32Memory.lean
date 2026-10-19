import InitECandidate.Solver.Input.RlpWrite.U256Store
import InitECandidate.Solver.WitnessRadix.AllocationExpected
import InitECandidate.Solver.MutableTable.FamilyAdvancePools
import InitECandidate.Solver.MutableTable.FamilyValuePools
import InitECandidate.Solver.Mpt.AccountRegistry
import InitECandidate.Solver.GasBudget.JournalZone
import InitECandidate.Solver.PanHeapGlobals

namespace InitECandidate.Solver.Mpt.Value32
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout

def allocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) := PersistentAlloc.nextState source "v" cursor (cursor + 32)
def stored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (words : Input.RlpWrite.U256Value.Words) :=
  {allocated source cursor with memory := WordWrites.write source.memory (Input.RlpWrite.U256Value.wordWrites (BitVec.ofNat 64 cursor) words)}

theorem writes_earlier (memory : WordWrites.Memory) (cursor : Nat) (words : Input.RlpWrite.U256Value.Words)
    (room : cursor + 32 ≤ 33806089496) (query : BitVec 64) (earlier : query.toNat < cursor) :
    WordWrites.write memory (Input.RlpWrite.U256Value.wordWrites (BitVec.ofNat 64 cursor) words) query = memory query := by
  apply WordWrites.write_away
  intro found
  simp only [Input.RlpWrite.U256Value.wordWrites,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at found
  have selected : ∃ offset : Nat,offset ≤ 24 ∧ query = BitVec.ofNat 64 (cursor + offset) := by
    rcases found with same | same | same | same
    · exact ⟨0,by decide,by simpa using same⟩
    · exact ⟨8,by decide,by simpa only [BitVec.ofNat_add] using same⟩
    · exact ⟨16,by decide,by simpa only [BitVec.ofNat_add] using same⟩
    · exact ⟨24,by decide,by simpa only [BitVec.ofNat_add] using same⟩
  obtain ⟨offset,inside,same⟩ := selected
  rw [same,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at earlier
  omega

theorem stored_models {ι : Type}
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor cutoff : Nat)
    (objects : ι → TableFamily.Object) (writer : ι) (accounts : List (BitVec 64))
    (family : TableFamily.Model source cursor objects) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property)
    (base cap count : Nat) (entries : Nat → GasBudget.Journal.Entry ι)
    (image : GasBudget.Journal.Image source objects base count entries) (zone : GasBudget.Journal.Zone objects base cap cursor) (countBound : count ≤ cap)
    (words : Input.RlpWrite.U256Value.Words) (room : cursor + 32 ≤ 33806089496) :
    TableFamily.Model (stored source cursor words) (cursor + 32) objects ∧
      GasBudget.Journal.Image (stored source cursor words) objects base count entries ∧ GasBudget.Journal.Zone objects base cap (cursor + 32) ∧
      AccountDecode.Registry (stored source cursor words) cutoff (cursor + 32) objects accounts ∧ TableFamily.ValuesHave (stored source cursor words) objects property ∧
      TableFamily.PersistentFrame 0 cursor objects objects source (stored source cursor words) ∧ HeapGlobals source (stored source cursor words) ∧
      AllocatedBytes.Arena (BitVec.ofNat 64 cursor) 32 ∧ (BitVec.ofNat 64 cursor).toNat % 8 = 0 := by
  let target := stored source cursor words
  have table := family.tables writer
  have cursorSmall : cursor < 2^64 := by omega
  have cursorNumber : (BitVec.ofNat 64 cursor).toNat = cursor := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt cursorSmall]
  have earlierWords (query : BitVec 64) (earlier : query.toNat < cursor) : target.memory query = source.memory query := writes_earlier source.memory cursor words room query earlier
  have pools : ∀ index,MemoryModel.PoolFrame source.memory target.memory (objects index).kind (objects index).plan := by
    intro index pool offset inside
    apply earlierWords
    rw [NaturalLayout.number (objects index).kind (objects index).plan (family.tables index).valid pool offset inside]
    have before := (family.tables index).earlier pool
    omega
  have nextFamily : TableFamily.Model target (cursor + 32) objects := family.advance_pools
    (by simp [target,stored,allocated,PersistentAlloc.nextState,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE])
    (by omega) room (by have := table.aligned; omega) rfl rfl pools
  have nextValues := values.of_pools source target objects cursor family property pools
  have frame : TableFamily.PersistentFrame 0 cursor objects objects source target := ⟨fun query lower earlier outside => ⟨outside,earlierWords query earlier⟩⟩
  have nextRegistry := registry.framed source target cutoff cursor (cursor + 32) objects objects accounts
    ⟨fun query above earlier outside => frame.words query (Nat.zero_le _) earlier outside⟩ (by omega) rfl
  have nextImage : GasBudget.Journal.Image target objects base count entries := image.transfer rfl (fun _ => rfl) (fun _ => rfl)
    (fun index inside field => earlierWords _ (GasBudget.Journal.entry_before base cap cursor index field zone.earlier cursorSmall (by omega))) image.separate
  have arena : AllocatedBytes.Arena (BitVec.ofNat 64 cursor) 32 := by
    constructor
    · rw [cursorNumber]
      have lower := table.valid.lower .header
      have before := table.earlier .header
      change (objects writer).plan.base .header + 72 ≤ cursor at before
      omega
    · rw [cursorNumber]
      exact room
  exact ⟨nextFamily,nextImage,zone.advance (by omega),nextRegistry,nextValues,frame,HeapGlobals.update source (BitVec.ofNat 64 (cursor + 32)),arena,by rw [cursorNumber]; exact table.aligned⟩

end InitECandidate.Solver.Mpt.Value32

#print axioms InitECandidate.Solver.Mpt.Value32.writes_earlier
#print axioms InitECandidate.Solver.Mpt.Value32.stored_models
