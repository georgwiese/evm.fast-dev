import InitECandidate.Solver.GasBudget.JournalAppendDeleteValues

namespace InitECandidate.Solver.GasBudget.Journal.Append
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

/-- Complete original jdel body. Its actual getter either yields an absent
key and a read-only return, or reaches the real guard/append/deletion path.
All clocks and physical postconditions follow from that normal execution. -/
theorem delete_body_normal {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (objects : ι → TableFamily.Object) (writer : ι)
    (base cap count : Nat) (entries : Nat → Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base count entries)
    (zone : Zone objects base cap cursor) (countBound : count ≤ cap) (environment : WarmKeys.Environment source)
    (query : BitVec 64)
    (queryFits : query.toNat + KeyHash.keySize (objects writer).kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize (objects writer).kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (objects writer).pointer)))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word query)))
    (getCode : source.code.lookup (ofString "htab_get") = some (Get.formals, Get.body, Get.pairShape))
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, Delete.body, .one))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source deleteBody = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧
      ((∃ paid, 1 ≤ paid ∧ paid ≤ Get.bodyPrice (objects writer).kind (objects writer).slots.length + 1 ∧ paid ≤ source.clock ∧
        emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with clock := source.clock - paid}) ∨
      (count < cap ∧ ∃ (paid : Nat) (next : TableFamily.Object) (oldValue : BitVec 64),
        1 ≤ paid ∧ paid ≤ deletePrice (objects writer).kind (objects writer).slots.length ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
        next.kind = (objects writer).kind ∧ next.plan = (objects writer).plan ∧
        TableFamily.Model post (cursor + NaturalLayout.stride (objects writer).kind) (Function.update objects writer next) ∧
        Image post (Function.update objects writer next) base (count + 1) (Function.update entries count ⟨writer, BitVec.ofNat 64 cursor, 1#64, oldValue⟩) ∧
        Zone (Function.update objects writer next) base cap (cursor + NaturalLayout.stride (objects writer).kind) ∧
        next.slots.length ≤ (objects writer).slots.length ∧
        post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + 1)))) ∧
        post.code = source.code ∧ WarmKeys.Environment post ∧ OtherGlobals source post)) := by
  obtain ⟨returnedEq,branches⟩ := delete_body_normal_values source post cursor objects writer base cap count entries family image zone countBound environment query
    (fun _ _=>True) (fun _ _ _ _ _ _=>True.intro) (fun _ _ _=>True.intro) queryFits queryMapped tableLocal keyLocal getCode deleteCode journal capacity counter returned normal
  refine ⟨returnedEq,?_⟩
  rcases branches with absent | present
  · exact Or.inl absent
  · obtain ⟨room,paid,next,oldValue,positive,bounded,fits,clock,kind,plan,models,nextImage,nextZone,population,nextCounter,codes,nextEnvironment,globals,frame,nextValues,nextSaved⟩ := present
    exact Or.inr ⟨room,paid,next,oldValue,positive,bounded,fits,clock,kind,plan,models,nextImage,nextZone,population,nextCounter,codes,nextEnvironment,globals⟩

end InitECandidate.Solver.GasBudget.Journal.Append

#print axioms InitECandidate.Solver.GasBudget.Journal.Append.delete_body_normal
