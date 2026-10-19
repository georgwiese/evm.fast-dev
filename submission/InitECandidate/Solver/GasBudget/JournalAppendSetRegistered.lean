import InitECandidate.Solver.GasBudget.JournalAppendSetCallValues

namespace InitECandidate.Solver.GasBudget.Journal.Append
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

/-- The real journaled setter retains registered account images through its
actual key copy, record writes and table growth, alongside live/saved values. -/
theorem set_call_registered_values {ι : Type} [DecidableEq ι]
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (objects : ι → TableFamily.Object) (writer : ι)
    (base cap count : Nat) (entries : Nat → Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Image source objects base count entries)
    (zone : Zone objects base cap cursor) (countBound : count ≤ cap) (environment : WarmKeys.Environment source)
    (cutoff : Nat) (accounts : List (BitVec 64)) (registry : Mpt.AccountDecode.Registry source cutoff cursor objects accounts)
    (accountApart : ∀ account,account∈accounts → account.toNat+56≤base ∨ base+32*cap≤account.toNat)
    (query value : BitVec 64)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (owned : property writer value)
    (savedValues : EntryValues entries count property)
    (queryFits : query.toNat + KeyHash.keySize (objects writer).kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize (objects writer).kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (getCode : source.code.lookup (ofString "htab_get") = some (Get.formals, Get.body, Get.pairShape))
    (code : source.code.lookup (ofString "jset") = some (TableCall.formals, setBody, .one))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (TableCall.values (objects writer).pointer query value))
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "jset") arguments) = (none, target)) :
    count < cap ∧ ∃ (paid nextCursor : Nat) (next : TableFamily.Object) (oldFlag oldValue : BitVec 64),
      1 ≤ paid ∧ paid ≤ source.clock ∧ target.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧ next.kind = (objects writer).kind ∧
      (oldFlag = 0#64 ∨ oldFlag = 1#64) ∧
      TableFamily.Model target nextCursor (Function.update objects writer next) ∧
      Image target (Function.update objects writer next) base (count + 1) (Function.update entries count ⟨writer, BitVec.ofNat 64 cursor, oldFlag, oldValue⟩) ∧
      Zone (Function.update objects writer next) base cap nextCursor ∧
      paid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity ≤
        setPrice (objects writer).kind (objects writer).slots.length + 1 + GrowRuntime.growthPotential (objects writer).kind next.plan.capacity ∧
      next.slots.length ≤ (objects writer).slots.length + 1 ∧
      target.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + 1)))) ∧
      target.locals = source.locals ∧ target.code = source.code ∧ WarmKeys.Environment target ∧ OtherGlobals source target ∧ CounterEffect source target 1 0 0 ∧ ProtectedFrame base cap cursor objects (Function.update objects writer next) source target ∧
      TableFamily.ValuesHave target (Function.update objects writer next) property ∧
      EntryValues (Function.update entries count ⟨writer,BitVec.ofNat 64 cursor,oldFlag,oldValue⟩) (count+1) property ∧ Mpt.AccountDecode.Registry target cutoff nextCursor (Function.update objects writer next) accounts ∧ TableFamily.Metadata objects (Function.update objects writer next) := by
  obtain ⟨room,paid,nextCursor,next,flag,oldValue,positive,fits,clock,forward,kind,binary,models,nextImage,nextZone,bounded,population,nextCounter,locals,codes,nextEnvironment,globals,effect,frame,nextValues,nextSaved,pointers⟩ :=
    set_call_normal_values source target cursor objects writer base cap count entries family image zone countBound environment query value
      property values owned savedValues queryFits queryMapped getCode code journal capacity counter arguments args normal
  have domain := nextEnvironment.domain.trans environment.domain.symm
  have nextRegistry := frame.registry source target base cap cutoff cursor nextCursor objects (Function.update objects writer next) accounts registry accountApart forward domain
  exact ⟨room,paid,nextCursor,next,flag,oldValue,positive,fits,clock,forward,kind,binary,models,nextImage,nextZone,bounded,population,nextCounter,locals,codes,nextEnvironment,globals,effect,frame,nextValues,nextSaved,nextRegistry,pointers⟩

end InitECandidate.Solver.GasBudget.Journal.Append

#print axioms InitECandidate.Solver.GasBudget.Journal.Append.set_call_registered_values
