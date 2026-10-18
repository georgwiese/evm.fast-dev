import InitECandidate.Solver.GasBudget.JournalSelect

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

/-- One actual selected rollback mutation, with a whole-family amortized
price. The branch and its arguments are read from the real journal record. -/
theorem selected_normal {ι : Type} [Fintype ι] [DecidableEq ι]
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (objects : ι → TableFamily.Object)
    (base cap count index population : Nat) (entries : Nat → Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base count entries)
    (zone : Zone objects base cap cursor) (countBound : count ≤ cap) (inside : index < count)
    (populations : ∀ table, (objects table).slots.length ≤ population)
    (environment : WarmKeys.Environment source)
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, Delete.body, .one))
    (locals : CallLocals source objects base index (entries index))
    (normal : evaluateHOLFiniteState source selectCall = (none, target)) :
    ∃ (paid nextCursor : Nat) (next : ι → TableFamily.Object),
      paid ≤ source.clock ∧ target.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      TableFamily.Model target nextCursor next ∧ Image target next base count entries ∧ Zone next base cap nextCursor ∧
      paid + TableFamily.potential objects ≤ 38 * population + 39 + TableFamily.potential next ∧
      (∀ table, (next table).slots.length ≤ population + 1) ∧
      target.locals = source.locals ∧ target.code = source.code ∧ WarmKeys.Environment target ∧ HeapGlobals source target ∧ TableFamily.FloorFrame objects next source target := by
  let writer := (entries index).writer
  have actual := select_read source objects base count index entries inside image locals
  rw [actual] at normal
  have populationBound := populations writer
  have priceBound := step_price_bound (objects writer).kind (objects writer).slots.length
  by_cases zero : (entries index).flag = 0#64
  · rw [if_pos zero] at normal
    obtain ⟨paid, next, bounded, fits, clock, kind, plan, models, nextImage, nextZone, populationUpper, localEq, globalEq, codes, nextEnvironment, floorFrame⟩ :=
      delete_zone_normal source target cursor objects writer base cap count entries family image zone environment (entries index).key
        (image.queryFits index inside) (image.queryMapped index inside) deleteCode _
        (delete_arguments source objects base index (entries index) locals) normal
    have maxBound := Nat.le_max_right (Set.noGrowthPrice (objects writer).kind (objects writer).slots.length + 1)
      (Delete.modelPrice (objects writer).kind (objects writer).slots.length + 1)
    change _ ≤ stepPrice (objects writer).kind (objects writer).slots.length at maxBound
    have potentialEq : next.potential = (objects writer).potential := by rw [TableFamily.Object.potential, kind, plan]; rfl
    have charged : paid + (objects writer).potential ≤ 38 * population + 39 + next.potential := by
      dsimp only [writer] at *
      omega
    refine ⟨paid, cursor, Function.update objects writer next, fits, clock, Nat.le_refl _, models, nextImage, nextZone,
      TableFamily.amortized_update objects writer next paid _ charged,
      TableFamily.population_update objects writer next population populations (by dsimp only [writer] at *; omega), localEq, codes, nextEnvironment, ?_, floorFrame⟩
    intro key different
    rw [globalEq]
  · rw [if_neg zero] at normal
    obtain ⟨paid, nextCursor, next, fits, clock, forward, kind, models, nextImage, nextZone, bounded, populationUpper, localEq, codes, nextEnvironment, globals, floorFrame⟩ :=
      set_zone_normal source target cursor objects writer base cap count entries family image zone countBound environment (entries index).key (entries index).value
        (image.queryFits index inside) (image.queryMapped index inside) _
        (set_arguments source objects base count index entries inside image locals) normal
    have maxBound := Nat.le_max_left (Set.noGrowthPrice (objects writer).kind (objects writer).slots.length + 1)
      (Delete.modelPrice (objects writer).kind (objects writer).slots.length + 1)
    change _ ≤ stepPrice (objects writer).kind (objects writer).slots.length at maxBound
    have charged : paid + (objects writer).potential ≤ 38 * population + 39 + next.potential := by
      simp only [TableFamily.Object.potential, kind]
      dsimp only [writer] at *
      omega
    exact ⟨paid, nextCursor, Function.update objects writer next, fits, clock, forward, models, nextImage, nextZone,
      TableFamily.amortized_update objects writer next paid _ charged,
      TableFamily.population_update objects writer next population populations populationUpper, localEq, codes, nextEnvironment, globals, floorFrame⟩

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.selected_normal
