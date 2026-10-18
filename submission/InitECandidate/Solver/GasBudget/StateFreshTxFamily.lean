import InitECandidate.Solver.GasBudget.StateFreshTxTailEffect
import InitECandidate.Solver.GasBudget.StateFreshTxIndices
import InitECandidate.Solver.GasBudget.JournalSnapshot

namespace InitECandidate.Solver.GasBudget.StateFreshTx
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout

def objectsAfter {ι : Type} (objects : ι → TableFamily.Object) (start : Nat) :
    (specs : List Spec) → Added specs.length ι → TableFamily.Object
  | [] => objects
  | spec :: specs => objectsAfter (TableFamily.extend objects (Journal.newObject spec.kind start spec.capacity))
      (freshEnd spec.kind start spec.capacity) specs

theorem objectsAfter_old {ι : Type} (specs : List Spec) (objects : ι → TableFamily.Object) (start : Nat) (index : ι) :
    objectsAfter objects start specs (embed specs.length index) = objects index := by
  induction specs generalizing ι start with
  | nil => rfl
  | cons spec specs ih => exact ih _ _ (some index)

theorem cursor_forward (specs : List Spec) (start : Nat) : start ≤ cursor start specs := by
  induction specs generalizing start with
  | nil => exact Nat.le_refl _
  | cons spec specs ih =>
    have next := ih (freshEnd spec.kind start spec.capacity)
    change start ≤ cursor (freshEnd spec.kind start spec.capacity) specs
    exact Nat.le_trans (by dsimp only [freshEnd]; omega) next

/-- The computed original constructor/store tail retains every old physical
table and adds each new empty table. The transaction record remains separate
from pools on both sides; the entire journal reservation remains protected.
Its final room premise is discharged by the actual-normal effect theorem. -/
theorem walk_family {ι : Type} (specs : List Spec) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (start tx : Nat) (objects : ι → TableFamily.Object) (base cap : Nat) (entries : Nat → Journal.Entry ι)
    (family : TableFamily.Model source start objects) (zone : Journal.Zone objects base cap start)
    (recordValid : MemoryRegion.Valid ⟨tx, 72⟩) (apart : TableFamily.ApartRegion objects ⟨tx, 72⟩)
    (afterRecord : tx + 72 ≤ start)
    (environment : WarmKeys.Environment source) (lower : 2701131776 ≤ start) (aligned : start % 8 = 0)
    (wellFormed : ∀ spec ∈ specs, spec.Valid) (room : cursor start specs ≤ 33806089496) :
    TableFamily.Model (walk source start tx specs) (cursor start specs) (objectsAfter objects start specs) ∧
      Journal.Zone (objectsAfter objects start specs) base cap (cursor start specs) ∧
      TableFamily.ApartRegion (objectsAfter objects start specs) ⟨tx, 72⟩ := by
  induction specs generalizing ι source start with
  | nil =>
    refine ⟨family.of_pools (target := walk source start tx []) ?_ rfl rfl (fun _ _ _ _ => rfl), zone, apart⟩
    exact Input.putGlobal.lookup_other source "journal_n" 0#64 (ofString "heap_ptr") (by decide)
  | cons spec specs ih =>
    have validSpec := wellFormed spec (by simp)
    have nextRoom : freshEnd spec.kind start spec.capacity ≤ 33806089496 :=
      Nat.le_trans (cursor_forward specs (freshEnd spec.kind start spec.capacity)) room
    have valid := fresh_valid spec.kind start spec.capacity (Nat.two_pow_pos _) lower nextRoom aligned
    have bounded : start ≤ 33806089496 := Nat.le_trans (cursor_forward (spec :: specs) start) room
    obtain ⟨positive, multiple, keySmall, wordSmall, capSmall⟩ := Journal.new_capacity_bounds spec.kind spec.capacity spec.bits rfl validSpec.1
      (Nat.pow_le_pow_right (by decide) validSpec.2.1)
    obtain ⟨constructedFamily, constructedImage, constructedZone, constructedEnvironment, constructedGlobals⟩ :=
      Journal.new_models source "t" start spec.capacity spec.bits spec.kind objects base cap 0 entries family
        (Journal.Image.empty _ _ _ _) zone (Nat.zero_le _) environment bounded rfl (Nat.le_trans (by decide : 2 ≤ 3) validSpec.1) multiple valid
    let constructed := TableRuntime.callState source "t" spec.kind start spec.capacity
    let newObjects := TableFamily.extend objects (Journal.newObject spec.kind start spec.capacity)
    have newApart : TableFamily.ApartRegion newObjects ⟨tx, 72⟩ := apart.extend (Journal.newObject spec.kind start spec.capacity) afterRecord
      (fun pool => (fresh_bounds spec.kind start spec.capacity pool).1)
    have nextFamily : TableFamily.Model (stepState source start tx spec) (freshEnd spec.kind start spec.capacity) newObjects :=
      constructedFamily.write_region ⟨tx, 72⟩ recordValid newApart spec.offset (by have := validSpec.2.2.2.1; change spec.offset < 72; omega) (BitVec.ofNat 64 start)
    have nextAligned : freshEnd spec.kind start spec.capacity % 8 = 0 := by
      have position := valid.aligned .position
      change ((fresh spec.kind start spec.capacity).base .position + 8 * spec.capacity) % 8 = 0
      rw [Nat.add_mod, position]
      omega
    have forward : start ≤ freshEnd spec.kind start spec.capacity := by dsimp only [freshEnd]; omega
    exact ih (source := stepState source start tx spec) (start := freshEnd spec.kind start spec.capacity) newObjects
      (fun index => (entries index).lift) nextFamily constructedZone newApart (by omega)
      (constructedEnvironment.of_fields rfl rfl rfl) (by omega) nextAligned
      (by intro next member; exact wellFormed next (by simp [member])) room

end InitECandidate.Solver.GasBudget.StateFreshTx

#print axioms InitECandidate.Solver.GasBudget.StateFreshTx.objectsAfter_old
#print axioms InitECandidate.Solver.GasBudget.StateFreshTx.cursor_forward
#print axioms InitECandidate.Solver.GasBudget.StateFreshTx.walk_family
