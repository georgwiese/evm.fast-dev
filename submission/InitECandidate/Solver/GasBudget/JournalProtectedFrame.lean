import InitECandidate.Solver.GasBudget.JournalAppendRecordEntry
import InitECandidate.Solver.GasBudget.JournalAppendKeyModel
import InitECandidate.Solver.Mpt.AccountRegistry
import InitECandidate.Solver.MutableTable.FamilyValuePools

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable NaturalLayout

def Away (base cap : Nat) (query : BitVec 64) : Prop := query.toNat<base ∨ base+32*cap≤query.toNat

/-- Actual append effects may touch journal words and live pools; earlier
words outside both retain their contents and pool separation. -/
structure ProtectedFrame {ι : Type} (base cap cursor : Nat) (objects next : ι → TableFamily.Object)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  words : ∀ query : BitVec 64,query.toNat<cursor → TableFamily.Outside objects query → Away base cap query →
    TableFamily.Outside next query ∧ target.memory query=source.memory query

theorem ProtectedFrame.of_persistent {ι : Type} (base cap cursor : Nat) (objects next : ι → TableFamily.Object)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame : TableFamily.PersistentFrame 0 cursor objects next source target) : ProtectedFrame base cap cursor objects next source target :=
  ⟨fun query earlier outside away=>frame.words query (Nat.zero_le _) earlier outside⟩

theorem ProtectedFrame.trans {ι : Type} {base cap cursor middleCursor : Nat} {objects middleObjects next : ι → TableFamily.Object}
    {source middle target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (first : ProtectedFrame base cap cursor objects middleObjects source middle)
    (second : ProtectedFrame base cap middleCursor middleObjects next middle target) (forward : cursor≤middleCursor) :
    ProtectedFrame base cap cursor objects next source target := by
  constructor
  intro query earlier outside away
  have left := first.words query earlier outside away
  have right := second.words query (by omega) left.1 away
  exact ⟨right.1,right.2.trans left.2⟩

/-- The actual four record stores preserve words outside the whole reserved
journal, and all occupied table values. Unused table cells are unconstrained. -/
theorem Append.recorded_protected {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (objects : ι → TableFamily.Object) (base cap count cursor : Nat) (entry : Entry ι)
    (family : TableFamily.Model source cursor objects) (zone : Zone objects base cap cursor) (room : count<cap)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) :
    ProtectedFrame base cap cursor objects objects source (Append.recorded source objects base count entry) ∧
      TableFamily.ValuesHave (Append.recorded source objects base count entry) objects property := by
  have pools : ∀ index,MemoryModel.PoolFrame source.memory (Append.recorded source objects base count entry).memory (objects index).kind (objects index).plan := by
    intro index pool offset inside
    apply WordWrites.write_away
    intro found
    simp only [recordWrites,List.map_map,Function.comp_def] at found
    obtain ⟨field,inRange,equal⟩ := List.mem_map.mp found
    exact zone.separate count room field index pool offset inside equal
  refine ⟨⟨?_⟩,values.of_pools source _ objects cursor family property pools⟩
  intro query earlier outside away
  refine ⟨outside,?_⟩
  apply WordWrites.write_away
  intro found
  simp only [recordWrites,List.map_map,Function.comp_def] at found
  obtain ⟨field,inRange,equal⟩ := List.mem_map.mp found
  have number := congrArg BitVec.toNat equal
  rw [entry_number base cap count field zone.valid room] at number
  have fieldBound := field.isLt
  rcases away with before | after <;> omega

theorem ProtectedFrame.registry {ι : Type} (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (base cap cutoff cursor nextCursor : Nat) (objects next : ι → TableFamily.Object) (accounts : List (BitVec 64))
    (frame : ProtectedFrame base cap cursor objects next source target)
    (registry : Mpt.AccountDecode.Registry source cutoff cursor objects accounts)
    (apart : ∀ account,account∈accounts → account.toNat+56≤base ∨ base+32*cap≤account.toNat)
    (forward : cursor≤nextCursor) (domain : target.memaddrs=source.memaddrs) :
    Mpt.AccountDecode.Registry target cutoff nextCursor next accounts := by
  have retained (account : BitVec 64) (member : account∈accounts) (offset : Nat) (inside : offset<56) :
      TableFamily.Outside next (account+BitVec.ofNat 64 offset) ∧ target.memory (account+BitVec.ofNat 64 offset)=source.memory (account+BitVec.ofNat 64 offset) := by
    obtain ⟨image⟩ := registry.images account member
    have number := image.output.slot_number account offset inside
    apply frame.words
    · rw [number]; have := registry.before account member; omega
    · exact registry.objectOutside account member offset inside
    · rw [Away,number]; rcases apart account member with before | after <;> omega
  refine ⟨registry.distinct,?_,registry.above,?_,registry.separated,fun account member offset inside=>(retained account member offset inside).1⟩
  · intro account member
    obtain ⟨image⟩ := registry.images account member
    exact ⟨image.of_agreement source target account domain (retained account member 40 (by decide)).2 (retained account member 48 (by decide)).2⟩
  · intro account member; have := registry.before account member; omega

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.ProtectedFrame.of_persistent
#print axioms InitECandidate.Solver.GasBudget.Journal.ProtectedFrame.trans
#print axioms InitECandidate.Solver.GasBudget.Journal.Append.recorded_protected
#print axioms InitECandidate.Solver.GasBudget.Journal.ProtectedFrame.registry
