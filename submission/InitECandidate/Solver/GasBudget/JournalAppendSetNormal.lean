import InitECandidate.Solver.GasBudget.JournalAppendSetValues

namespace InitECandidate.Solver.GasBudget.Journal.Append
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

/-- Complete original jset body on actual normal execution. The getter,
guard, key allocation/copy, real record stores, increment and final setter
derive the next journal image and whole table family. No helper execution,
intermediate model, future allocation room or source-clock budget is given. -/
theorem set_body_normal {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (objects : ι → TableFamily.Object) (writer : ι)
    (base cap count : Nat) (entries : Nat → Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base count entries)
    (zone : Zone objects base cap cursor) (countBound : count ≤ cap) (environment : WarmKeys.Environment source)
    (query value : BitVec 64)
    (queryFits : query.toNat + KeyHash.keySize (objects writer).kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize (objects writer).kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (objects writer).pointer)))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word query)))
    (valueLocal : source.locals.lookup (ofString "value") = some (.val (.word value)))
    (getCode : source.code.lookup (ofString "htab_get") = some (Get.formals, Get.body, Get.pairShape))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source setBody = (some (.returned returned), post)) :
    count < cap ∧ returned = .val (.word 0#64) ∧ ∃ (paid nextCursor : Nat) (next : TableFamily.Object) (oldFlag oldValue : BitVec 64),
      paid ≤ source.clock ∧ post.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧ next.kind = (objects writer).kind ∧
      (oldFlag = 0#64 ∨ oldFlag = 1#64) ∧
      TableFamily.Model post nextCursor (Function.update objects writer next) ∧
      Image post (Function.update objects writer next) base (count + 1) (Function.update entries count ⟨writer, BitVec.ofNat 64 cursor, oldFlag, oldValue⟩) ∧
      Zone (Function.update objects writer next) base cap nextCursor ∧
      paid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity ≤
        setPrice (objects writer).kind (objects writer).slots.length + GrowRuntime.growthPotential (objects writer).kind next.plan.capacity ∧
      next.slots.length ≤ (objects writer).slots.length + 1 ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + 1)))) ∧
      post.code = source.code ∧ WarmKeys.Environment post ∧ OtherGlobals source post := by
  obtain ⟨room,returnedEq,paid,nextCursor,next,flag,oldValue,fits,clock,forward,kind,binary,models,nextImage,nextZone,bounded,population,nextCounter,codes,nextEnvironment,globals,frame,nextValues,savedValues,_pointers⟩ :=
    set_body_normal_values source post cursor objects writer base cap count entries family image zone countBound environment query value
      (fun _ _=>True) (fun _ _ _ _ _ _=>True.intro) True.intro (fun _ _ _=>True.intro) queryFits queryMapped tableLocal keyLocal valueLocal getCode journal capacity counter returned normal
  exact ⟨room,returnedEq,paid,nextCursor,next,flag,oldValue,fits,clock,forward,kind,binary,models,nextImage,nextZone,bounded,population,nextCounter,codes,nextEnvironment,globals⟩

end InitECandidate.Solver.GasBudget.Journal.Append

#print axioms InitECandidate.Solver.GasBudget.Journal.Append.set_body_normal
