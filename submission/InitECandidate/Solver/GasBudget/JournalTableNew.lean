import InitECandidate.Solver.GasBudget.JournalFamilyExtend
import InitECandidate.Solver.GasBudget.WarmKeysInvariant
import InitECandidate.Solver.MutableTable.FamilyMemoryFrame
import InitECandidate.Solver.MutableTable.TableRuntime.NormalRoom
import InitECandidate.Solver.MutableTable.TableRuntime.Normal

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout

def newObject (kind : KeyHash.Kind) (start capacity : Nat) : TableFamily.Object :=
  ⟨kind, fresh kind start capacity, [], start⟩

theorem new_capacity_bounds (kind : KeyHash.Kind) (capacity bits : Nat) (power : capacity = 2 ^ bits)
    (minimum : 3 ≤ bits) (bounded : capacity ≤ 2 ^ 32) :
    0 < capacity ∧ capacity % 8 = 0 ∧ stride kind * capacity < 2 ^ 64 ∧ 8 * capacity < 2 ^ 64 ∧ capacity + 32 < 2 ^ 64 := by
  have positive : 0 < capacity := by rw [power]; exact Nat.pow_pos (by decide)
  have factor : capacity = 2 ^ (bits - 3) * 8 := by
    rw [power, show bits = (bits - 3) + 3 from by omega, Nat.pow_add]
    rfl
  have multiple : capacity % 8 = 0 := by simp [factor, Nat.mul_mod]
  have strideBound : stride kind ≤ 64 := by cases kind <;> decide
  have product := Nat.mul_le_mul_right capacity strideBound
  exact ⟨positive, multiple, by omega, by omega, by omega⟩

theorem new_models {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (start capacity bits : Nat) (kind : KeyHash.Kind) (objects : ι → TableFamily.Object)
    (base cap count : Nat) (entries : Nat → Entry ι)
    (family : TableFamily.Model source start objects) (image : Image source objects base count entries)
    (zone : Zone objects base cap start) (countBound : count ≤ cap) (environment : WarmKeys.Environment source)
    (bounded : start ≤ 33806089496) (power : capacity = 2 ^ bits) (minimum : 2 ≤ bits)
    (multiple : capacity % 8 = 0) (valid : Valid kind (fresh kind start capacity)) :
    TableFamily.Model (TableRuntime.callState source name kind start capacity) (freshEnd kind start capacity) (TableFamily.extend objects (newObject kind start capacity)) ∧
      Image (TableRuntime.callState source name kind start capacity) (TableFamily.extend objects (newObject kind start capacity)) base count (fun index => (entries index).lift) ∧
      Zone (TableFamily.extend objects (newObject kind start capacity)) base cap (freshEnd kind start capacity) ∧
      WarmKeys.Environment (TableRuntime.callState source name kind start capacity) ∧ HeapGlobals source (TableRuntime.callState source name kind start capacity) := by
  let target := TableRuntime.callState source name kind start capacity
  have nextBound : freshEnd kind start capacity ≤ 33806089496 := valid.upper .position
  have nextAligned : freshEnd kind start capacity % 8 = 0 := by
    have position := valid.aligned .position
    change ((fresh kind start capacity).base .position + 8 * capacity) % 8 = 0
    rw [Nat.add_mod, position]
    omega
  have forward : start ≤ freshEnd kind start capacity := by dsimp only [freshEnd]; omega
  have targetHeap : target.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (freshEnd kind start capacity)))) := by
    simp [target, TableRuntime.callState, WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have words (address : BitVec 64) (before : address.toNat < start) : target.memory address = source.memory address :=
    TableRuntime.caller_memory_away source name kind start capacity valid address (Or.inl before)
  let moved := {source with globals := target.globals}
  have movedFamily : TableFamily.Model moved (freshEnd kind start capacity) objects :=
    family.advance_cursor targetHeap forward nextBound nextAligned rfl rfl rfl
  have oldFamily : TableFamily.Model target (freshEnd kind start capacity) objects :=
    movedFamily.of_earlier_words (target := target) (cut := start) rfl rfl rfl (fun index => (family.tables index).earlier) words
  have freshTable : TableState target kind (fresh kind start capacity) [] (freshEnd kind start capacity) start :=
    ⟨valid, by simp, TableRuntime.caller_header source name kind start capacity valid,
      TableRuntime.caller_model source name kind start capacity valid (Or.inr multiple) environment.domain environment.little,
      ⟨bits, power, by omega⟩, targetHeap, nextBound, nextAligned, fun pool => (fresh_bounds kind start capacity pool).2,
      fun pool => (fresh_bounds kind start capacity pool).1⟩
  have newFamily := oldFamily.extend (newObject kind start capacity) freshTable (fun index => (family.tables index).earlier)
  have nextZone := zone.extend (newObject kind start capacity) valid (Nat.le_refl _) (fun pool => (fresh_bounds kind start capacity pool).1) forward
  have oldImage : Image target objects base count entries := by
    apply image.transfer (target := target) rfl (fun _ => rfl) (fun _ => rfl) _ image.separate
    intro index inside field
    exact words _ (entry_before base cap start index field zone.earlier (by omega) (by omega))
  have newImage := oldImage.extend (newObject kind start capacity) nextZone countBound
  exact ⟨newFamily, newImage, nextZone, environment.of_fields rfl rfl rfl, HeapGlobals.update source _⟩

/-- An actual original constructor extends the live table identity family,
preserving the existing journal and every older pool. The normal execution
derives its fresh layout, reached room and exact constructor clock. -/
theorem new_call_normal {ι : Type} (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (start capacity bits : Nat) (kind : KeyHash.Kind) (objects : ι → TableFamily.Object)
    (base cap count : Nat) (entries : Nat → Entry ι)
    (family : TableFamily.Model source start objects) (image : Image source objects base count entries)
    (zone : Zone objects base cap start) (countBound : count ≤ cap) (environment : WarmKeys.Environment source)
    (lower : 2701131776 ≤ start) (bounded : start ≤ 33806089496) (aligned : start % 8 = 0)
    (power : capacity = 2 ^ bits) (minimum : 3 ≤ bits) (capBound : capacity ≤ 2 ^ 32)
    (newCode : source.code.lookup (ofString "htab_new") = some (TableNew.formals, TableNew.body, .one))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (TableRuntime.values kind capacity))
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_new") arguments continuation) = (some (.returned returned), post)) :
    TableRuntime.price capacity + 1 ≤ source.clock ∧ ∃ finish,
      evaluateHOLFiniteState (TableRuntime.callState source name kind start capacity) continuation = (some (.returned returned), finish) ∧
      post = restore source name finish ∧
      TableFamily.Model (TableRuntime.callState source name kind start capacity) (freshEnd kind start capacity) (TableFamily.extend objects (newObject kind start capacity)) ∧
      Image (TableRuntime.callState source name kind start capacity) (TableFamily.extend objects (newObject kind start capacity)) base count (fun index => (entries index).lift) ∧
      Zone (TableFamily.extend objects (newObject kind start capacity)) base cap (freshEnd kind start capacity) ∧
      WarmKeys.Environment (TableRuntime.callState source name kind start capacity) ∧ HeapGlobals source (TableRuntime.callState source name kind start capacity) := by
  obtain ⟨positive, multiple, keySmall, wordSmall, capSmall⟩ := new_capacity_bounds kind capacity bits power minimum capBound
  have valid := TableRuntime.normal_call_layout source post kind start capacity name arguments continuation positive lower bounded aligned keySmall wordSmall capSmall multiple
    environment.domain args newCode heap environment.allocCode environment.trapCode environment.zeroCode returned normal
  obtain ⟨funded, finish, actual, restored⟩ := TableRuntime.call_normal source post kind start capacity name arguments continuation valid environment.domain (Or.inr multiple)
    args newCode heap environment.allocCode environment.zeroCode returned normal
  have models := new_models source name start capacity bits kind objects base cap count entries family image zone countBound environment bounded power (by omega) multiple valid
  exact ⟨funded, finish, actual, restored, models⟩

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.new_capacity_bounds
#print axioms InitECandidate.Solver.GasBudget.Journal.new_models
#print axioms InitECandidate.Solver.GasBudget.Journal.new_call_normal
