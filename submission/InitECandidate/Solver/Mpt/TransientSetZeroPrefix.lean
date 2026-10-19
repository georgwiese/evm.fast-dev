import InitECandidate.Solver.Mpt.TransientSetAfterZero
import InitECandidate.Solver.Input.NormalCallClock

namespace InitECandidate.Solver.Mpt.TransientSet
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

theorem zero_prefix_normal {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (query transaction : BitVec 64) (words : Input.RlpWrite.U256Value.Words)
    (cursor cutoff : Nat) (objects : ι → TableFamily.Object) (writer : ι)
    (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (accounts : List (BitVec 64)) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (accountApart : ∀ account,account ∈ accounts → account.toNat + 56 ≤ base ∨ base + 32 * cap ≤ account.toNat)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (savedValues : Journal.EntryValues entries count property)
    (freshOwned : ∀ pointer,AllocatedBytes.Arena pointer 32 → pointer.toNat % 8 = 0 → property writer pointer)
    (writerKind : (objects writer).kind = .storage) (queryArena : AllocatedBytes.Arena query 52)
    (queryLocal : source.locals.lookup (ofString "k") = some (.val (.word query)))
    (valueLocal : source.locals.lookup (ofString "value") = some (Input.RlpWrite.U256Value.tuple words))
    (transactionGlobal : source.globals.lookup (ofString "ts") = some (.val (.word transaction)))
    (tableMapped : source.memaddrs (transaction + 64#64)) (tableStored : source.memory (transaction + 64#64) = .word (objects writer).pointer)
    (tableBefore : (transaction + 64#64).toNat < cursor)
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterKey = (some (.returned returned),post)) :
    returned = .val (.word 0#64) ∧ ∃ (removed : Bool) (paid nextCursor : Nat) (next : ι → TableFamily.Object) (nextEntries : Nat → Journal.Entry ι) (added : Nat),
      paid ≤ source.clock ∧ post.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧ added ≤ 1 ∧ count + added ≤ cap ∧
      TableFamily.Model post nextCursor next ∧ Journal.Image post next base (count + added) nextEntries ∧ Journal.Zone next base cap nextCursor ∧
      paid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity ≤
        1 + (if removed then Journal.Append.deletePrice (objects writer).kind (objects writer).slots.length + 1 else Journal.Append.setPrice (objects writer).kind (objects writer).slots.length + 2) + GrowRuntime.growthPotential (objects writer).kind (next writer).plan.capacity ∧
      post.code = source.code ∧ WarmKeys.Environment post ∧ Journal.OtherGlobals source post ∧ TableFamily.ValuesHave post next property ∧
      Journal.EntryValues nextEntries (count + added) property ∧ AccountDecode.Registry post cutoff nextCursor next accounts ∧
      Journal.CounterEffect source post added 0 0 ∧ Journal.ProtectedFrame base cap cursor objects next source post ∧ TableFamily.Metadata objects next ∧
      (∀ reader,reader ≠ writer → next reader = objects reader) ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + added)))) ∧
      (next writer).slots.length ≤ (objects writer).slots.length + 1 ∧ removed = decide (U256Zero.resultWord words ≠ 0#64) ∧ (removed = false → added = 1) := by
  classical
  have positive := Input.CallNormal.normal_clock source post (ofString "z") .one (ofString "u256_is_zero") [localVar "value"] afterZero returned normal
  have args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) [localVar "value"] = some [Input.RlpWrite.U256Value.tuple words] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,valueLocal]
  have execute := U256Zero.call_execute source words "z" [localVar "value"] afterZero args (U256Zero.original_code source.code installed) positive
  change evaluateHOLFiniteState source (.decCall (ofString "z") .one (ofString "u256_is_zero") [localVar "value"] afterZero) = _ at normal
  rw [execute] at normal
  let ready := bind {source with clock := source.clock - 1} "z" (U256Zero.resultWord words)
  let inner := (evaluateHOLFiniteState ready afterZero).2
  have resultEq := congrArg Prod.fst normal
  change (evaluateHOLFiniteState ready afterZero).1 = some (.returned returned) at resultEq
  have tailRun : evaluateHOLFiniteState ready afterZero = (some (.returned returned),inner) := Prod.ext resultEq rfl
  have scope := congrArg Prod.snd normal
  change restore source "z" inner = post at scope
  have readyFamily : TableFamily.Model ready cursor objects := family.of_control rfl rfl rfl rfl
  have readyImage : Journal.Image ready objects base count entries := image.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate
  have readyRegistry := registry.framed source ready cutoff cursor cursor objects objects accounts
    (TableFamily.PersistentFrame.of_memory cutoff cursor objects source ready rfl) (Nat.le_refl _) rfl
  have readyQuery : ready.locals.lookup (ofString "k") = some (.val (.word query)) :=
    (bind_lookup_other _ "z" "k" _ (by decide)).trans queryLocal
  have readyValue : ready.locals.lookup (ofString "value") = some (Input.RlpWrite.U256Value.tuple words) :=
    (bind_lookup_other _ "z" "value" _ (by decide)).trans valueLocal
  have readyZero : ready.locals.lookup (ofString "z") = some (.val (.word (U256Zero.resultWord words))) := bind_lookup_same _ _ _
  obtain ⟨answerEq,removed,paid,nextCursor,next,nextEntries,added,funded,clock,forward,addedBound,capacityBound,models,nextImage,nextZone,price,codes,nextEnvironment,globals,
    nextValues,nextSaved,nextRegistry,effect,frame,metadata,others,nextCounter,population,decision,appends⟩ := after_zero_normal ready inner query transaction (U256Zero.resultWord words) words
      cursor cutoff objects writer base cap count entries readyFamily readyImage zone countBound (environment.of_fields rfl rfl rfl) installed accounts readyRegistry accountApart property values savedValues
      freshOwned writerKind queryArena readyQuery readyZero readyValue transactionGlobal tableMapped tableStored tableBefore journal capacity counter returned tailRun
  rw [← scope]
  let finish := restore source "z" inner
  have finalFamily : TableFamily.Model finish nextCursor next := models.of_control rfl rfl rfl rfl
  have finalImage : Journal.Image finish next base (count + added) nextEntries := nextImage.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) nextImage.separate
  have finalRegistry := nextRegistry.framed inner finish cutoff nextCursor nextCursor next next accounts
    (TableFamily.PersistentFrame.of_memory cutoff nextCursor next inner finish rfl) (Nat.le_refl _) rfl
  change paid ≤ source.clock - 1 at funded
  change inner.clock = source.clock - 1 - paid at clock
  have totalFunded : 1 + paid ≤ source.clock := by omega
  have totalClock : inner.clock = source.clock - (1 + paid) := by omega
  exact ⟨answerEq,removed,1 + paid,nextCursor,next,nextEntries,added,totalFunded,totalClock,forward,addedBound,capacityBound,finalFamily,finalImage,nextZone,by omega,
    codes,nextEnvironment.of_fields rfl rfl rfl,globals,nextValues,nextSaved,finalRegistry,effect,⟨frame.words⟩,metadata,others,nextCounter,population,decision,appends⟩

end InitECandidate.Solver.Mpt.TransientSet

#print axioms InitECandidate.Solver.Mpt.TransientSet.zero_prefix_normal
