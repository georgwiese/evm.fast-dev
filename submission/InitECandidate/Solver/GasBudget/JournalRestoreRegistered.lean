import InitECandidate.Solver.GasBudget.JournalRestoreCallValues
import InitECandidate.Solver.Mpt.AccountRegistry

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

/-- The complete actual rollback caller retains real registered account
objects and occupied cache/undo values through every reached mutation. -/
theorem restore_call_registered_values {ι : Type} [Fintype ι] [DecidableEq ι]
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (objects : ι → TableFamily.Object)
    (base cap count snap population : Nat) (entries : Nat → Entry ι) (ordered : snap ≤ count) (small : count < 2 ^ 64)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base count entries)
    (zone : Zone objects base cap cursor) (countBound : count ≤ cap) (populations : ∀ table, (objects table).slots.length ≤ population)
    (cutoff : Nat) (accounts : List (BitVec 64)) (registry : Mpt.AccountDecode.Registry source cutoff cursor objects accounts)
    (environment : WarmKeys.Environment source)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (savedValues : EntryValues entries count property)
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, Delete.body, .one))
    (code : source.code.lookup (ofString "state_restore") = some (formals, body, .one))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word (BitVec.ofNat 64 snap))])
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "state_restore") arguments) = (none, target)) :
    ∃ (paid nextCursor : Nat) (next : ι → TableFamily.Object),
      1 ≤ paid ∧ paid ≤ source.clock ∧ target.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      TableFamily.Model target nextCursor next ∧ Image target next base snap entries ∧ Zone next base cap nextCursor ∧
      paid + TableFamily.potential objects ≤ price population (count - snap) + 1 + TableFamily.potential next ∧
      (∀ table, (next table).slots.length ≤ population + (count - snap)) ∧
      target.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 snap))) ∧
      target.locals = source.locals ∧ target.code = source.code ∧ WarmKeys.Environment target ∧ OtherGlobals source target ∧ TableFamily.FloorFrame objects next source target ∧
      TableFamily.PersistentFrame 0 cursor objects next source target ∧ TableFamily.ValuesHave target next property ∧ EntryValues entries snap property ∧ Mpt.AccountDecode.Registry target cutoff nextCursor next accounts := by
  obtain ⟨paid,nextCursor,next,positive,funded,clock,forward,models,nextImage,nextZone,priceBound,populationsAfter,nextCounter,locals,codeEq,nextEnvironment,globals,floorFrame,persistent,nextValues,nextSaved⟩ :=
    restore_call_normal_values source target cursor objects base cap count snap population entries ordered small family image zone countBound populations environment
      property values savedValues deleteCode code journal counter arguments args normal
  have frame : TableFamily.PersistentFrame cutoff cursor objects next source target :=
    ⟨fun query lower earlier outside=>persistent.words query (Nat.zero_le _) earlier outside⟩
  have nextRegistry := registry.framed source target cutoff cursor nextCursor objects next accounts frame forward (nextEnvironment.domain.trans environment.domain.symm)
  exact ⟨paid,nextCursor,next,positive,funded,clock,forward,models,nextImage,nextZone,priceBound,populationsAfter,nextCounter,locals,codeEq,nextEnvironment,globals,floorFrame,persistent,nextValues,nextSaved,nextRegistry⟩

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.restore_call_registered_values
