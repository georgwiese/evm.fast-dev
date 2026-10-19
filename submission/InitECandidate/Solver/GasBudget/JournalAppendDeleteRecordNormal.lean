import InitECandidate.Solver.GasBudget.JournalAppendDeleteRecordValues

namespace InitECandidate.Solver.GasBudget.Journal.Append
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

/-- Complete original post-copy jdel suffix with its literal saved flag1,
actual record stores, counter increment, deletion and zero return. -/
theorem delete_record_normal {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (objects : ι → TableFamily.Object) (writer : ι)
    (base cap count : Nat) (entries : Nat → Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base count entries)
    (zone : Zone objects base cap cursor) (room : count < cap) (environment : WarmKeys.Environment source)
    (query copiedKey oldValue : BitVec 64)
    (queryFits : query.toNat + KeyHash.keySize (objects writer).kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize (objects writer).kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (copiedFits : copiedKey.toNat + KeyHash.keySize (objects writer).kind < 2 ^ 64)
    (copiedMapped : ∀ offset < KeyHash.keySize (objects writer).kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress copiedKey offset)))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (objects writer).pointer)))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word query)))
    (copyLocal : source.locals.lookup (ofString "kc") = some (.val (.word copiedKey)))
    (old : source.locals.lookup (ofString "old") = some (Get.pair 1#64 oldValue))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, Delete.body, .one))
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source deleteAfterCopy = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧ ∃ (paid : Nat) (next : TableFamily.Object),
      paid ≤ Delete.modelPrice (objects writer).kind (objects writer).slots.length + 1 ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
      next.kind = (objects writer).kind ∧ next.plan = (objects writer).plan ∧
      TableFamily.Model post cursor (Function.update objects writer next) ∧
      Image post (Function.update objects writer next) base (count + 1) (Function.update entries count ⟨writer, copiedKey, 1#64, oldValue⟩) ∧
      Zone (Function.update objects writer next) base cap cursor ∧ next.slots.length ≤ (objects writer).slots.length ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + 1)))) ∧
      post.code = source.code ∧ WarmKeys.Environment post ∧ OtherGlobals source post := by
  obtain ⟨returnedEq,paid,next,bounded,fits,clock,kind,plan,models,nextImage,nextZone,population,nextCounter,codes,nextEnvironment,globals,frame,nextValues,_pointers⟩ :=
    delete_record_normal_values source post cursor objects writer base cap count entries family image zone room environment query copiedKey oldValue (fun _ _=>True) (fun _ _ _ _ _ _=>True.intro)
      queryFits queryMapped copiedFits copiedMapped tableLocal keyLocal copyLocal old journal counter deleteCode returned normal
  exact ⟨returnedEq,paid,next,bounded,fits,clock,kind,plan,models,nextImage,nextZone,population,nextCounter,codes,nextEnvironment,globals⟩

end InitECandidate.Solver.GasBudget.Journal.Append

#print axioms InitECandidate.Solver.GasBudget.Journal.Append.delete_record_normal
