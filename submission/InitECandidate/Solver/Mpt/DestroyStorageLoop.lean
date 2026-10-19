import InitECandidate.Solver.Mpt.DestroyStorageBody
import InitECandidate.Solver.Input.LoopNormal

namespace InitECandidate.Solver.Mpt.DestroyStorage
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

theorem loop_normal {ι : Type} [DecidableEq ι] (remaining : Nat)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (address scratch transaction : BitVec 64)
    (cursor cutoff : Nat) (objects : ι → TableFamily.Object) (writer reader : ι)
    (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (accounts : List (BitVec 64)) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (owned : property writer 1#64)
    (writerKind : (objects writer).kind = .storage) (readerKind : (objects reader).kind = .word)
    (addressArena : AllocatedBytes.Arena address 20) (scratchArena : AllocatedBytes.Arena scratch 52)
    (floors : ∀ index, cutoff ≤ (objects index).floor) (scratchBelow : scratch.toNat + 52 ≤ cutoff)
    (small : cutoff < 2^64) (journalAbove : cutoff ≤ base)
    (addressLocal : source.locals.lookup (ofString "addr") = some (.val (.word address)))
    (readerLocal : source.locals.lookup (ofString "inner") = some (.val (.word (objects reader).pointer)))
    (scratchGlobal : source.globals.lookup (ofString "sk_buf") = some (.val (.word scratch)))
    (transactionGlobal : source.globals.lookup (ofString "ts") = some (.val (.word transaction)))
    (tableMapped : source.memaddrs (transaction + 24#64))
    (tableStored : source.memory (transaction + 24#64) = .word (objects writer).pointer)
    (tableAbove : cutoff ≤ (transaction + 24#64).toNat)
    (index : Nat) (countEq : index + remaining = (objects reader).slots.length) (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (countLocal : source.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 (objects reader).slots.length))))
    (tableBefore : (transaction + 24#64).toNat < cursor) (tableOutside : TableFamily.Outside objects (transaction + 24#64))
    (normal : evaluateHOLFiniteState source loop = (none,post)) :
    ∃ (paid nextCursor : Nat) (next : ι → TableFamily.Object), paid ≤ source.clock ∧ post.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      TableFamily.Model post nextCursor next ∧ Journal.Image post next base count entries ∧ Journal.Zone next base cap nextCursor ∧
      paid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity ≤
        loopPrice (objects writer).slots.length remaining + GrowRuntime.growthPotential (objects writer).kind (next writer).plan.capacity ∧
      (next writer).slots.length ≤ (objects writer).slots.length + remaining ∧ next reader = objects reader ∧
      post.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (objects reader).slots.length))) ∧ post.code = source.code ∧
      WarmKeys.Environment post ∧ HeapGlobals source post ∧ TableFamily.ValuesHave post next property ∧
      AccountDecode.Registry post cutoff nextCursor next accounts ∧ TableFamily.PersistentFrame cutoff cursor objects next source post ∧ TableFamily.Metadata objects next ∧ (∀ table, table ≠ writer → next table = objects table) := by
  induction remaining generalizing source cursor objects index with
  | zero =>
    have finished : index = (objects reader).slots.length := by omega
    have countSmall := live_count_small source (objects reader) cursor (family.tables reader)
    have encoded : (BitVec.ofNat 64 (objects reader).slots.length).toNat = (objects reader).slots.length := by
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have test := condition_read source (BitVec.ofNat 64 index) (BitVec.ofNat 64 (objects reader).slots.length)
      (by rw [finished,encoded]; omega) (by rw [encoded]; exact countSmall) indexLocal countLocal
    rw [finished,if_neg (by omega)] at test
    have actual : evaluateHOLFiniteState source loop = (none,source) := by
      simp only [eval,evalHOLFinite] at test
      rw [loop,evaluateHOLFiniteState_while_total]
      simp only [evalHOLFinite,test]
      simp
    have same := congrArg Prod.snd (normal.symm.trans actual)
    change post = source at same
    subst post
    exact ⟨0,cursor,objects,by omega,by simp,Nat.le_refl _,family,image,zone,by simp [loopPrice,WitnessBuild.triangle],by simp,rfl,
      by simpa only [finished] using indexLocal,rfl,environment,HeapGlobals.refl source,values,registry,TableFamily.PersistentFrame.refl cutoff cursor objects source,TableFamily.Metadata.refl objects,(fun _ _ => rfl)⟩
  | succ remaining ih =>
    have countSmall := live_count_small source (objects reader) cursor (family.tables reader)
    have indexBound : index < (objects reader).slots.length := by omega
    have encodedCount : (BitVec.ofNat 64 (objects reader).slots.length).toNat = (objects reader).slots.length := by
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have encodedIndex : (BitVec.ofNat 64 index).toNat = index := by
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have test := condition_read source (BitVec.ofNat 64 index) (BitVec.ofNat 64 (objects reader).slots.length)
      (by rw [encodedIndex]; omega) (by rw [encodedCount]; exact countSmall) indexLocal countLocal
    rw [encodedIndex,encodedCount,if_pos indexBound] at test
    obtain ⟨positive,middle,bodyRun,tailRun,clockBound⟩ := Input.while_none_step source post (ofString "cap") condition loopBody
      (loop_body_safe (ofString "cap") (by decide) (by decide) (by decide)) test normal
    let entry := decClockHOLFinite source
    have entryFamily : TableFamily.Model entry cursor objects := family.of_control rfl rfl rfl rfl
    have entryImage : Journal.Image entry objects base count entries := image.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate
    have entryRegistry := registry.framed source entry cutoff cursor cursor objects objects accounts
      (TableFamily.PersistentFrame.of_memory cutoff cursor objects source entry rfl) (Nat.le_refl _) rfl
    obtain ⟨paid,middleCursor,nextObject,funded,clock,forward,middleFamily,middleImage,middleZone,bodyPrice,population,middleIndex,codes,middleEnvironment,globals,
      middleValues,middleRegistry,bodyFrame,metadata⟩ := body_normal entry middle address scratch transaction cursor cutoff objects writer reader base cap count entries
        entryFamily entryImage zone countBound (environment.of_fields rfl rfl rfl) installed accounts entryRegistry property values owned writerKind readerKind
        addressArena scratchArena floors scratchBelow small journalAbove addressLocal readerLocal scratchGlobal transactionGlobal tableMapped tableStored tableAbove
        ⟨index,indexBound⟩ indexLocal bodyRun
    let middleObjects := Function.update objects writer nextObject
    have different : reader ≠ writer := by
      intro same
      rw [same,writerKind] at readerKind
      cases readerKind
    have readerSame : middleObjects reader = objects reader := Function.update_of_ne different _ _
    have middleWriterKind : (middleObjects writer).kind = .storage := (metadata.kinds writer).trans writerKind
    have middleReaderKind : (middleObjects reader).kind = .word := by rw [readerSame]; exact readerKind
    have localFrame (name : String) (notS : ofString name ≠ ofString "s") (notK : ofString name ≠ ofString "k") (notI : ofString name ≠ ofString "i") :
        middle.locals.lookup (ofString name) = source.locals.lookup (ofString name) := by
      have info := (loop_body_safe (ofString name) notS notK notI).summary entry
      rw [bodyRun] at info
      exact info.1 rfl
    have middleAddress := (localFrame "addr" (by decide) (by decide) (by decide)).trans addressLocal
    have middleReader : middle.locals.lookup (ofString "inner") = some (.val (.word (middleObjects reader).pointer)) := by
      rw [metadata.pointers reader]
      exact (localFrame "inner" (by decide) (by decide) (by decide)).trans readerLocal
    have middleCount : middle.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 (middleObjects reader).slots.length))) := by
      rw [readerSame]
      exact (localFrame "cap" (by decide) (by decide) (by decide)).trans countLocal
    have middleScratch := (globals (ofString "sk_buf") (by decide)).trans scratchGlobal
    have middleTransaction := (globals (ofString "ts") (by decide)).trans transactionGlobal
    have middleInstalled : Input.OriginalCode.Installed middle.code := by rw [codes]; exact installed
    have middleFloors (table : ι) : cutoff ≤ (middleObjects table).floor := by rw [metadata.floors table]; exact floors table
    have cellFrame := bodyFrame.words (transaction + 24#64) tableAbove tableBefore tableOutside
    have middleStored : middle.memory (transaction + 24#64) = .word (middleObjects writer).pointer := by
      rw [metadata.pointers writer]
      exact cellFrame.2.trans tableStored
    have middleMapped : middle.memaddrs (transaction + 24#64) := by
      rw [middleEnvironment.domain,← environment.domain]
      exact tableMapped
    obtain ⟨restPaid,nextCursor,next,restFunded,restClock,restForward,nextFamily,nextImage,nextZone,restPrice,nextPopulation,readerFinal,finalIndex,finalCodes,
      finalEnvironment,finalGlobals,finalValues,finalRegistry,restFrame,restMetadata,restObjects⟩ := ih
        (source := middle) (cursor := middleCursor) (objects := middleObjects) middleFamily middleImage middleZone middleEnvironment middleInstalled middleRegistry middleValues
        middleWriterKind middleReaderKind middleFloors middleAddress middleReader middleScratch middleTransaction middleMapped middleStored
        (index := index + 1) (by rw [readerSame]; omega) middleIndex middleCount (by omega) cellFrame.1 tailRun
    change paid ≤ source.clock - 1 at funded
    change middle.clock = source.clock - 1 - paid at clock
    have nextPrice := loop_price_mono (middleObjects writer).slots.length ((objects writer).slots.length + 1) remaining (by simpa only [middleObjects,Function.update_self] using population)
    rw [metadata.kinds writer] at restPrice
    have writerSame : middleObjects writer = nextObject := by simp [middleObjects]
    rw [writerSame] at restPrice nextPrice nextPopulation
    have headFrame : TableFamily.PersistentFrame cutoff cursor objects middleObjects source middle := ⟨bodyFrame.words⟩
    refine ⟨1 + paid + restPaid,nextCursor,next,by omega,by omega,by omega,nextFamily,nextImage,nextZone,?_,?_,readerFinal.trans readerSame,
      ?_,finalCodes.trans codes,finalEnvironment,(show HeapGlobals source middle from globals).trans finalGlobals,finalValues,finalRegistry,
      headFrame.trans restFrame forward,metadata.trans restMetadata,?_⟩
    · rw [loop_price_step]
      omega
    · change (next writer).slots.length ≤ _
      change nextObject.slots.length ≤ (objects writer).slots.length + 1 at population
      have bound := nextPopulation
      change (next writer).slots.length ≤ nextObject.slots.length + remaining at bound
      omega
    · simpa only [readerSame] using finalIndex
    · intro table other
      exact (restObjects table other).trans (Function.update_of_ne other nextObject objects)

end InitECandidate.Solver.Mpt.DestroyStorage

#print axioms InitECandidate.Solver.Mpt.DestroyStorage.loop_normal
