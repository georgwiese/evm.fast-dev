import InitECandidate.Solver.GasBudget.JournalAppendDeleteTailValues

namespace InitECandidate.Solver.GasBudget.Journal.Append
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

/-- Original post-store jdel tail increments the counter, deletes with the
original query and returns zero. Every live/unused journal slot survives. -/
theorem delete_tail_normal {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (objects : ι → TableFamily.Object) (writer : ι)
    (base cap count : Nat) (entries : Nat → Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base (count + 1) entries)
    (zone : Zone objects base cap cursor) (environment : WarmKeys.Environment source) (query : BitVec 64)
    (queryFits : query.toNat + KeyHash.keySize (objects writer).kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize (objects writer).kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (objects writer).pointer)))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word query)))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, Delete.body, .one))
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (afterStores deleteAfterCopy) = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧ ∃ (paid : Nat) (next : TableFamily.Object),
      paid ≤ Delete.modelPrice (objects writer).kind (objects writer).slots.length + 1 ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
      next.kind = (objects writer).kind ∧ next.plan = (objects writer).plan ∧
      TableFamily.Model post cursor (Function.update objects writer next) ∧
      Image post (Function.update objects writer next) base (count + 1) entries ∧ Zone (Function.update objects writer next) base cap cursor ∧
      next.slots.length ≤ (objects writer).slots.length ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + 1)))) ∧
      post.code = source.code ∧ WarmKeys.Environment post ∧ OtherGlobals source post := by
  obtain ⟨returnedEq,paid,next,bounded,fits,clock,kind,plan,models,nextImage,nextZone,population,nextCounter,codes,nextEnvironment,globals,persistent,nextValues⟩ :=
    delete_tail_normal_values source post cursor objects writer base cap count entries family image zone environment query (fun _ _=>True) (fun _ _ _ _ _ _=>True.intro) queryFits queryMapped tableLocal keyLocal counter deleteCode returned normal
  exact ⟨returnedEq,paid,next,bounded,fits,clock,kind,plan,models,nextImage,nextZone,population,nextCounter,codes,nextEnvironment,globals⟩

end InitECandidate.Solver.GasBudget.Journal.Append

#print axioms InitECandidate.Solver.GasBudget.Journal.Append.delete_tail_normal
