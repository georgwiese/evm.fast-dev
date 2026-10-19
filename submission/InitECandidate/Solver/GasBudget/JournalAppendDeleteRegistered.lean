import InitECandidate.Solver.GasBudget.JournalAppendDeleteCallValues

namespace InitECandidate.Solver.GasBudget.Journal.Append
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

/-- Complete actual journaled deletion retains current registered accounts,
live/saved values and all physical journal/table models in both branches. -/
theorem delete_call_registered_values {ι : Type} [DecidableEq ι]
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (objects : ι → TableFamily.Object) (writer : ι)
    (base cap count : Nat) (entries : Nat → Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base count entries)
    (zone : Zone objects base cap cursor) (countBound : count ≤ cap) (environment : WarmKeys.Environment source)
    (cutoff : Nat) (accounts : List (BitVec 64)) (registry : Mpt.AccountDecode.Registry source cutoff cursor objects accounts)
    (accountApart : ∀ account,account∈accounts → account.toNat+56≤base ∨ base+32*cap≤account.toNat)
    (query : BitVec 64)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (savedValues : EntryValues entries count property)
    (queryFits : query.toNat + KeyHash.keySize (objects writer).kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize (objects writer).kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (getCode : source.code.lookup (ofString "htab_get") = some (Get.formals, Get.body, Get.pairShape))
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, Delete.body, .one))
    (code : source.code.lookup (ofString "jdel") = some (Find.formals, deleteBody, .one))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word (objects writer).pointer), .val (.word query)])
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "jdel") arguments)=(none,target)) :
    ∃ paid nextCursor nextObjects nextEntries added,
      paid≤deletePrice (objects writer).kind (objects writer).slots.length+1 ∧ paid≤source.clock ∧ target.clock=source.clock-paid ∧
      cursor≤nextCursor ∧ added≤1 ∧ count+added≤cap ∧ TableFamily.Model target nextCursor nextObjects ∧
      Mpt.AccountDecode.Registry target cutoff nextCursor nextObjects accounts ∧
      Image target nextObjects base (count+added) nextEntries ∧ Zone nextObjects base cap nextCursor ∧
      TableFamily.ValuesHave target nextObjects property ∧ EntryValues nextEntries (count+added) property ∧
      CounterEffect source target added 0 0 ∧ ProtectedFrame base cap cursor objects nextObjects source target ∧
      target.code=source.code ∧ WarmKeys.Environment target ∧ OtherGlobals source target := by
  have branches := delete_call_normal_values source target cursor objects writer base cap count entries family image zone countBound environment query
    property values savedValues queryFits queryMapped getCode deleteCode code journal capacity counter arguments args normal
  rcases branches with absent | present
  · obtain ⟨paid,positive,bounded,funded,canonical,effect⟩ := absent
    subst target
    have frame : ProtectedFrame base cap cursor objects objects source {source with clock:=source.clock-paid} :=
      ⟨fun query earlier outside away=>⟨outside,rfl⟩⟩
    refine ⟨paid,cursor,objects,entries,0,?_,funded,rfl,Nat.le_refl _,by decide,by simpa using countBound,
      family.of_control rfl rfl rfl rfl,?_,?_,zone,values,?_,effect,frame,rfl,environment.of_fields rfl rfl rfl,?_⟩
    · dsimp only [deletePrice]; omega
    · exact registry.framed source _ cutoff cursor cursor objects objects accounts
        (TableFamily.PersistentFrame.of_memory cutoff cursor objects source _ rfl) (Nat.le_refl _) rfl
    · exact image.transfer rfl (fun _=>rfl) (fun _=>rfl) (fun _ _ _=>rfl) image.separate
    · simpa only [Nat.add_zero] using savedValues
    · intro key heap different; rfl
  · obtain ⟨room,paid,next,oldValue,positive,bounded,funded,clock,kind,plan,models,nextImage,nextZone,population,nextCounter,locals,codes,nextEnvironment,globals,effect,frame,nextValues,nextSaved⟩ := present
    have nextRegistry := frame.registry source target base cap cutoff cursor (cursor+NaturalLayout.stride (objects writer).kind)
      objects (Function.update objects writer next) accounts registry accountApart (by omega) (nextEnvironment.domain.trans environment.domain.symm)
    exact ⟨paid,cursor+NaturalLayout.stride (objects writer).kind,Function.update objects writer next,
      Function.update entries count ⟨writer,BitVec.ofNat 64 cursor,1#64,oldValue⟩,1,bounded,funded,clock,by omega,Nat.le_refl _,by omega,
      models,nextRegistry,nextImage,nextZone,nextValues,nextSaved,effect,frame,codes,nextEnvironment,globals⟩

end InitECandidate.Solver.GasBudget.Journal.Append

#print axioms InitECandidate.Solver.GasBudget.Journal.Append.delete_call_registered_values
