import InitECandidate.Solver.GasBudget.JournalZoneSetValues

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

/-- An arbitrary actual setter retains the entire journal reservation,
including unused slots, as well as its live prefix image. This applies to
the final append mutation with the original query rather than its copy. -/
theorem set_zone_normal {ι : Type} [DecidableEq ι] (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (cursor : Nat) (objects : ι → TableFamily.Object) (writer : ι) (base cap count : Nat) (entries : Nat → Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base count entries)
    (zone : Zone objects base cap cursor) (countBound : count ≤ cap)
    (environment : WarmKeys.Environment source) (query value : BitVec 64)
    (queryFits : query.toNat + KeyHash.keySize (objects writer).kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize (objects writer).kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments =
      some (TableCall.values (objects writer).pointer query value))
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "htab_set") arguments) = (none, target)) :
    ∃ (paid nextCursor : Nat) (next : TableFamily.Object),
      paid ≤ source.clock ∧ target.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧ next.kind = (objects writer).kind ∧
      TableFamily.Model target nextCursor (Function.update objects writer next) ∧
      Image target (Function.update objects writer next) base count entries ∧ Zone (Function.update objects writer next) base cap nextCursor ∧
      paid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity ≤
        Set.noGrowthPrice (objects writer).kind (objects writer).slots.length + 1 + GrowRuntime.growthPotential (objects writer).kind next.plan.capacity ∧
      next.slots.length ≤ (objects writer).slots.length + 1 ∧ target.locals = source.locals ∧ target.code = source.code ∧
      WarmKeys.Environment target ∧ HeapGlobals source target ∧ TableFamily.FloorFrame objects (Function.update objects writer next) source target := by
  obtain ⟨paid,nextCursor,next,fits,clock,forward,kind,models,nextImage,nextZone,bounded,population,locals,codes,nextEnvironment,globals,floorFrame,persistent,nextValues,_pointers⟩ :=
    set_zone_normal_values source target cursor objects writer base cap count entries family image zone countBound environment query value
      (fun _ _=>True) (fun _ _ _ _ _ _=>True.intro) True.intro queryFits queryMapped arguments args normal
  exact ⟨paid,nextCursor,next,fits,clock,forward,kind,models,nextImage,nextZone,bounded,population,locals,codes,nextEnvironment,globals,floorFrame⟩

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.set_zone_normal
