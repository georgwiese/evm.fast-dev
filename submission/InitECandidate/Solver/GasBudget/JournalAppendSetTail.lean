import InitECandidate.Solver.GasBudget.JournalAppendSetTailValues

namespace InitECandidate.Solver.GasBudget.Journal.Append
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

/-- The real original append tail increments journal_n, performs its actual
setter with the original key, then returns zero. It retains all live record
images and unused journal slots across any reached table growth. -/
theorem set_tail_normal {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (objects : ι → TableFamily.Object) (writer : ι)
    (base cap count : Nat) (entries : Nat → Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base (count + 1) entries)
    (zone : Zone objects base cap cursor) (room : count < cap) (environment : WarmKeys.Environment source)
    (query value : BitVec 64)
    (queryFits : query.toNat + KeyHash.keySize (objects writer).kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize (objects writer).kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (objects writer).pointer)))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word query)))
    (valueLocal : source.locals.lookup (ofString "value") = some (.val (.word value)))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (afterStores setAfterCopy) = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧ ∃ (paid nextCursor : Nat) (next : TableFamily.Object),
      paid ≤ source.clock ∧ post.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧ next.kind = (objects writer).kind ∧
      TableFamily.Model post nextCursor (Function.update objects writer next) ∧
      Image post (Function.update objects writer next) base (count + 1) entries ∧ Zone (Function.update objects writer next) base cap nextCursor ∧
      paid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity ≤
        Set.noGrowthPrice (objects writer).kind (objects writer).slots.length + 1 + GrowRuntime.growthPotential (objects writer).kind next.plan.capacity ∧
      next.slots.length ≤ (objects writer).slots.length + 1 ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + 1)))) ∧
      post.code = source.code ∧ WarmKeys.Environment post ∧ OtherGlobals source post := by
  obtain ⟨returnedEq,paid,nextCursor,next,fits,clock,forward,kind,models,nextImage,nextZone,bounded,population,nextCounter,codes,nextEnvironment,globals,persistent,nextValues⟩ :=
    set_tail_normal_values source post cursor objects writer base cap count entries family image zone room environment query value
      (fun _ _=>True) (fun _ _ _ _ _ _=>True.intro) True.intro queryFits queryMapped tableLocal keyLocal valueLocal counter returned normal
  exact ⟨returnedEq,paid,nextCursor,next,fits,clock,forward,kind,models,nextImage,nextZone,bounded,population,nextCounter,codes,nextEnvironment,globals⟩

end InitECandidate.Solver.GasBudget.Journal.Append

#print axioms InitECandidate.Solver.GasBudget.Journal.Append.set_tail_normal
