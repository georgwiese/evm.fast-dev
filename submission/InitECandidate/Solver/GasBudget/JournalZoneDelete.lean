import InitECandidate.Solver.GasBudget.JournalZoneDeleteValues

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

/-- An actual original deletion with any mapped query retains the complete
journal reservation and its live image. Table plans and heap stay fixed. -/
theorem delete_zone_normal {ι : Type} [DecidableEq ι] (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (cursor : Nat) (objects : ι → TableFamily.Object) (writer : ι) (base cap count : Nat) (entries : Nat → Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base count entries)
    (zone : Zone objects base cap cursor) (environment : WarmKeys.Environment source) (query : BitVec 64)
    (queryFits : query.toNat + KeyHash.keySize (objects writer).kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize (objects writer).kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, Delete.body, .one))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments =
      some [.val (.word (objects writer).pointer), .val (.word query)])
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "htab_del") arguments) = (none, target)) :
    ∃ (paid : Nat) (next : TableFamily.Object), paid ≤ Delete.modelPrice (objects writer).kind (objects writer).slots.length + 1 ∧
      paid ≤ source.clock ∧ target.clock = source.clock - paid ∧ next.kind = (objects writer).kind ∧ next.plan = (objects writer).plan ∧
      TableFamily.Model target cursor (Function.update objects writer next) ∧
      Image target (Function.update objects writer next) base count entries ∧ Zone (Function.update objects writer next) base cap cursor ∧
      next.slots.length ≤ (objects writer).slots.length ∧ target.locals = source.locals ∧ target.globals = source.globals ∧
      target.code = source.code ∧ WarmKeys.Environment target ∧ TableFamily.FloorFrame objects (Function.update objects writer next) source target := by
  obtain ⟨paid,next,bounded,fits,clock,kind,plan,models,nextImage,nextZone,population,locals,globals,codes,nextEnvironment,floorFrame,persistent,nextValues⟩ :=
    delete_zone_normal_values source target cursor objects writer base cap count entries family image zone environment query (fun _ _=>True) (fun _ _ _ _ _ _=>True.intro) queryFits queryMapped deleteCode arguments args normal
  exact ⟨paid,next,bounded,fits,clock,kind,plan,models,nextImage,nextZone,population,locals,globals,codes,nextEnvironment,floorFrame⟩

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.delete_zone_normal
