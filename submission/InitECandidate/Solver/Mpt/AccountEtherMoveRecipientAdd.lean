import InitECandidate.Solver.Mpt.AccountEtherMoveProgram
import InitECandidate.Solver.Mpt.AccountObjectReads
import InitECandidate.Solver.Mpt.AccountBalanceMutationReturn

namespace InitECandidate.Solver.Mpt.AccountEtherMove
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget AccountBalanceSet

def recipientAdd : ProgHOL 64 := .call (some (some (.local,ofString "nb"),none)) (ofString "u256_add") (balanceArguments "r")

theorem recipient_add_normal {ι : Type} [Fintype ι] [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (address account emptyHash scratch transaction : BitVec 64)
    (cursor cutoff protectedCursor populationBound : Nat) (objects : ι → TableFamily.Object) (writer outer accountWriter : ι)
    (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (population : ∀ index,(objects index).slots.length ≤ populationBound)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (accounts : List (BitVec 64)) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (owned : property writer 1#64) (accountOwned : property accountWriter 1#64) (publishOwned : property accountWriter account) (savedValues : Journal.EntryValues entries count property)
    (writerKind : (objects writer).kind = .storage) (outerKind : (objects outer).kind = .account) (accountKind : (objects accountWriter).kind = .account) (differentOuter : accountWriter ≠ outer)
    (addressArena : AllocatedBytes.Arena address 20) (scratchArena : AllocatedBytes.Arena scratch 52)
    (floors : ∀ index, cutoff ≤ (objects index).floor) (scratchBelow : scratch.toNat + 52 ≤ cutoff)
    (small : cutoff < 2^64) (journalAbove : cutoff ≤ base)
    (accountMember : account ∈ accounts) (protectedBefore : protectedCursor ≤ account.toNat)
    (amount oldNb : Input.RlpWrite.U256Value.Words)
    (addressLocal : source.locals.lookup (ofString "recipient") = some (.val (.word address)))
    (accountLocal : source.locals.lookup (ofString "r") = some (.val (.word account)))
    (amountLocal : source.locals.lookup (ofString "amount") = some (Input.RlpWrite.U256Value.tuple amount))
    (nbLocal : source.locals.lookup (ofString "nb") = some (Input.RlpWrite.U256Value.tuple oldNb))
    (emptyGlobal : source.globals.lookup (ofString "empty_code_hash") = some (.val (.word emptyHash)))
    (emptyArena : AllocatedBytes.Arena emptyHash 32)
    (innerReferences : ∀ item, property outer item → ∃ reader, (objects reader).pointer = item ∧ (objects reader).kind = .word)
    (scratchGlobal : source.globals.lookup (ofString "sk_buf") = some (.val (.word scratch)))
    (transactionGlobal : source.globals.lookup (ofString "ts") = some (.val (.word transaction)))
    (tableMapped : source.memaddrs (transaction + 24#64))
    (tableStored : source.memory (transaction + 24#64) = .word (objects writer).pointer)
    (tableAbove : cutoff ≤ (transaction + 24#64).toNat)
    (tableAway : Journal.Away base cap (transaction + 24#64))
    (tableBefore : (transaction + 24#64).toNat < protectedCursor) (tableOutside : TableFamily.Outside objects (transaction + 24#64))
    (outerMapped : source.memaddrs (transaction + 32#64))
    (outerStored : source.memory (transaction + 32#64) = .word (objects outer).pointer)
    (outerBefore : (transaction + 32#64).toNat < protectedCursor)
    (outerOutside : TableFamily.Outside objects (transaction + 32#64)) (outerAway : Journal.Away base cap (transaction + 32#64))
    (accountMapped : source.memaddrs (transaction + 16#64))
    (accountStored : source.memory (transaction + 16#64) = .word (objects accountWriter).pointer)
    (accountAbove : cutoff ≤ (transaction + 16#64).toNat) (accountBefore : (transaction + 16#64).toNat < protectedCursor)
    (accountOutside : TableFamily.Outside objects (transaction + 16#64)) (accountAway : Journal.Away base cap (transaction + 16#64))
    (accountApart : ∀ account,account ∈ accounts → account.toNat + 56 ≤ base ∨ base + 32 * cap ≤ account.toNat)
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.seq recipientAdd recipientCommit) = (some (.returned returned),post)) :
    returned = .val (.word 0#64) ∧ ∃ (empty : BitVec 64) (destroyed found : Bool) (iterations paid nextCursor : Nat) (next : ι → TableFamily.Object) (nextEntries : Nat → Journal.Entry ι) (added : Nat),
      1 ≤ paid ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧ 1 ≤ added ∧ added ≤ 3 ∧ count + added ≤ cap ∧
      TableFamily.Model post nextCursor next ∧ Journal.Image post next base (count + added) nextEntries ∧ Journal.Zone next base cap nextCursor ∧
      paid + TableFamily.potential objects ≤ commitPrice (objects writer).slots.length (objects outer).slots.length (objects accountWriter).slots.length destroyed found iterations + 1 + TableFamily.potential next ∧
      post.code = source.code ∧ WarmKeys.Environment post ∧ Journal.OtherGlobals source post ∧ TableFamily.ValuesHave post next property ∧
      Journal.EntryValues nextEntries (count + added) property ∧ AccountDecode.Registry post cutoff nextCursor next accounts ∧
      Journal.CounterEffect source post added 0 0 ∧ TableFamily.Metadata objects next ∧
      (∀ query : BitVec 64, cutoff ≤ query.toNat → query.toNat < protectedCursor → TableFamily.Outside objects query → Journal.Away base cap query →
        TableFamily.Outside next query ∧ post.memory query = source.memory query) ∧
      (∀ table, table ≠ writer → table ≠ outer → table ≠ accountWriter → next table = objects table) ∧
      ((found = false ∧ iterations = 0) ∨
        (found = true ∧ ∃ reader, (objects reader).kind = .word ∧ iterations = (objects reader).slots.length)) ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + added)))) ∧ destroyed = decide (empty ≠ 0#64) ∧ (empty = 0#64 ∨ empty = 1#64) ∧ (if destroyed then 2 ≤ added else added = 1 ∧ found = false ∧ iterations = 0) ∧ (next outer).plan = (objects outer).plan ∧
      (next writer).slots.length ≤ (objects writer).slots.length + iterations ∧ (next outer).slots.length ≤ (objects outer).slots.length ∧ (next accountWriter).slots.length ≤ (objects accountWriter).slots.length + 2 ∧ iterations ≤ populationBound ∧ (∀ index,(next index).slots.length ≤ populationBound + iterations + 2) := by
  classical
  have safe : Input.LocalPrefix (ofString "recipient") recipientAdd := .call (some (ofString "nb")) _ _ (by
    intro name same
    have equal : name = ofString "nb" := Option.some.inj same.symm
    rw [equal]
    decide)
  obtain ⟨assigned,addRun,tailRun,keepAddress⟩ := safe.normal_continue source post recipientCommit returned normal
  obtain ⟨accountImage⟩ := registry.images account accountMember
  let oldWords := Input.RlpWrite.U256Value.memoryWords source (account + 8#64)
  let newWords := U256Add.result oldWords amount
  have loadRead : evalHOLExact (toExact source) (.load Input.RlpWrite.U256Value.tupleShape (.op .add [localVar "r",.const 8#64])) = some (Input.RlpWrite.U256Value.tuple oldWords) := accountImage.balance_read_at source account "r" accountLocal
  have args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) (balanceArguments "r") =
      some [Input.RlpWrite.U256Value.tuple oldWords,Input.RlpWrite.U256Value.tuple amount] := by
    rw [evalListHOLFinite,balanceArguments,evalListHOLExact,loadRead]
    simp [evalListHOLExact,evalHOLExact,localVar,toExact,amountLocal]
  obtain ⟨addFunded,assignedEq⟩ := U256Add.assigned source assigned oldWords amount oldNb "nb" (balanceArguments "r") nbLocal args (U256Add.original_code source.code installed) addRun
  subst assigned
  let ready := setVarHOLFinite (ofString "nb") (Input.RlpWrite.U256Value.tuple newWords) {source with clock := source.clock - 1}
  have readyFamily : TableFamily.Model ready cursor objects := family.of_control rfl rfl rfl rfl
  have readyRegistry := registry.framed source ready cutoff cursor cursor objects objects accounts (TableFamily.PersistentFrame.of_memory cutoff cursor objects source ready rfl) (Nat.le_refl _) rfl
  have readyImage : Journal.Image ready objects base count entries := image.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate
  have readyAddress : ready.locals.lookup (ofString "recipient") = some (.val (.word address)) := by
    simpa [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "nb" ≠ ofString "recipient" by decide] using addressLocal
  have readyAccount : ready.locals.lookup (ofString "r") = some (.val (.word account)) := by
    simpa [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "nb" ≠ ofString "r" by decide] using accountLocal
  have readValue : eval ready (localVar "nb") = some (Input.RlpWrite.U256Value.tuple newWords) := by
    simp [eval,evalHOLExact,localVar,toExact,ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have grouped : evaluateHOLFiniteState ready (.seq (balanceCommit "recipient" "r" (localVar "nb")) (.return (.const 0#64))) = (some (.returned returned),post) :=
    (MemeqByteRuntime.sequence_assoc ready (storeBalanceAt "r" (localVar "nb")) (commitAccounts "recipient" "r") (.return (.const 0#64))).trans tailRun
  obtain ⟨answerEq,empty,destroyed,found,iterations,paid,nextCursor,next,nextEntries,added,paymentPositive,funded,clock,forward,addedPositive,addedBound,capacityBound,models,nextImage,nextZone,price,codes,nextEnvironment,globals,
    nextValues,nextSaved,nextRegistry,effect,metadata,frame,others,branch,nextCounter,decision,binary,appends,outerPlan,markerPopulation,outerPopulation,accountPopulation,visits,populations⟩ := balance_commit_return_normal ready post address account emptyHash scratch transaction
    cursor cutoff protectedCursor populationBound objects writer outer accountWriter base cap count entries population readyFamily readyImage zone countBound (environment.of_fields rfl rfl rfl) installed accounts readyRegistry property values owned accountOwned publishOwned savedValues
    writerKind outerKind accountKind differentOuter addressArena scratchArena floors scratchBelow small journalAbove accountMember protectedBefore "recipient" "r" newWords (localVar "nb") readyAddress readyAccount readValue
    emptyGlobal emptyArena innerReferences scratchGlobal transactionGlobal tableMapped tableStored tableAbove tableAway tableBefore tableOutside outerMapped outerStored outerBefore outerOutside outerAway accountMapped accountStored accountAbove accountBefore accountOutside accountAway accountApart journal capacity counter returned grouped
  change paid ≤ source.clock - 1 at funded
  change post.clock = source.clock - 1 - paid at clock
  exact ⟨answerEq,empty,destroyed,found,iterations,1 + paid,nextCursor,next,nextEntries,added,by omega,by omega,by omega,forward,addedPositive,addedBound,capacityBound,models,nextImage,nextZone,by omega,
    codes,nextEnvironment,globals,nextValues,nextSaved,nextRegistry,effect,metadata,frame,others,branch,nextCounter,decision,binary,appends,outerPlan,markerPopulation,outerPopulation,accountPopulation,visits,populations⟩

end InitECandidate.Solver.Mpt.AccountEtherMove

#print axioms InitECandidate.Solver.Mpt.AccountEtherMove.recipient_add_normal
