import InitECandidate.Solver.GasBudget.StateFreshTxScopedEffect
import InitECandidate.Solver.GasBudget.StateFreshTxFields

namespace InitECandidate.Solver.GasBudget.StateFreshTx
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout

theorem scoped_code (spec : Spec) (specs : List Spec) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start tx : Nat) :
    (scopedState spec specs source start tx).code = source.code := by
  change (walk (stepState source start tx spec) (freshEnd spec.kind start spec.capacity) tx specs).code = _
  rw [walk_code]
  rfl

theorem scoped_counter (spec : Spec) (specs : List Spec) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start tx : Nat) :
    (scopedState spec specs source start tx).globals.lookup (ofString "journal_n") = some (.val (.word 0#64)) :=
  walk_counter specs _ _ _

/-- Physical table identities, pointer fields and journal reservation on the
computed state of the first scoped constructor and its actual tail. -/
theorem scoped_owned {ι : Type} (spec : Spec) (specs : List Spec) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (start tx : Nat) (objects : ι → TableFamily.Object) (base cap : Nat) (entries : Nat → Journal.Entry ι)
    (family : TableFamily.Model source start objects) (zone : Journal.Zone objects base cap start)
    (recordValid : MemoryRegion.Valid ⟨tx, 72⟩) (apart : TableFamily.ApartRegion objects ⟨tx, 72⟩)
    (afterRecord : tx + 72 ≤ start)
    (environment : WarmKeys.Environment source) (lower : 2701131776 ≤ start) (aligned : start % 8 = 0)
    (wellFormed : ∀ next ∈ spec :: specs, next.Valid) (distinct : ((spec :: specs).map Spec.offset).Nodup)
    (room : cursor start (spec :: specs) ≤ 33806089496) :
    TableFamily.Model (scopedState spec specs source start tx) (cursor start (spec :: specs)) (objectsAfter objects start (spec :: specs)) ∧
      Journal.Zone (objectsAfter objects start (spec :: specs)) base cap (cursor start (spec :: specs)) ∧
      TableFamily.ApartRegion (objectsAfter objects start (spec :: specs)) ⟨tx, 72⟩ ∧
      Fields (scopedState spec specs source start tx) tx (objectsAfter objects start (spec :: specs)) (spec :: specs) ∧
      (scopedState spec specs source start tx).memory (MemoryRegion.address ⟨tx, 72⟩ 0) = source.memory (MemoryRegion.address ⟨tx, 72⟩ 0) := by
  obtain ⟨allTables, allZone, allApart⟩ := walk_family (spec :: specs) source start tx objects base cap entries family zone recordValid apart
    afterRecord environment lower aligned wellFormed room
  have fields := walk_fields (spec :: specs) source start tx objects recordValid afterRecord lower aligned wellFormed distinct room
  refine ⟨allTables.of_control rfl rfl rfl rfl, allZone, allApart, fields, ?_⟩
  exact walk_word (spec :: specs) source start tx lower aligned wellFormed room _ (by
    rw [MemoryRegion.address_number ⟨tx, 72⟩ recordValid 0 (by change 0 ≤ 72; decide)]
    change tx + 0 < start
    omega) (by
      intro next member
      have valid := wellFormed next member
      apply record_word_distinct tx recordValid 0 next.offset (by decide) (by have := valid.2.2.2.1; omega)
      have := valid.2.2.1
      omega)

end InitECandidate.Solver.GasBudget.StateFreshTx

#print axioms InitECandidate.Solver.GasBudget.StateFreshTx.scoped_counter
#print axioms InitECandidate.Solver.GasBudget.StateFreshTx.scoped_code
#print axioms InitECandidate.Solver.GasBudget.StateFreshTx.scoped_owned
