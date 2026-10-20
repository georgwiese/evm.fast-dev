import InitECandidate.Solver.Mpt.AccountEtherMoveSenderCopy

namespace InitECandidate.Solver.Mpt.AccountEtherMove
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget AccountBalanceSet

theorem sender_compare_prefix {ι : Type} [Fintype ι] [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (address account emptyHash scratch transaction : BitVec 64)
    (cursor cutoff protectedCursor populationBound : Nat) (objects : ι → TableFamily.Object) (writer outer accountWriter : ι)
    (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (population : ∀ index,(objects index).slots.length ≤ populationBound)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (accounts : List (BitVec 64)) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (owned : property writer 1#64) (accountOwned : property accountWriter 1#64) (savedValues : Journal.EntryValues entries count property)
    (writerKind : (objects writer).kind = .storage) (outerKind : (objects outer).kind = .account) (accountKind : (objects accountWriter).kind = .account) (differentOuter : accountWriter ≠ outer)
    (addressArena : AllocatedBytes.Arena address 20) (scratchArena : AllocatedBytes.Arena scratch 52)
    (floors : ∀ index, cutoff ≤ (objects index).floor) (scratchBelow : scratch.toNat + 52 ≤ cutoff)
    (small : cutoff < 2^64) (journalAbove : cutoff ≤ base)
    (accountMember : account ∈ accounts) (protect : protectedCursor ≤ cursor)
    (words : Input.RlpWrite.U256Value.Words)
    (addressLocal : source.locals.lookup (ofString "sender") = some (.val (.word address)))
    (accountLocal : source.locals.lookup (ofString "s") = some (.val (.word account)))
    (amountLocal : source.locals.lookup (ofString "amount") = some (Input.RlpWrite.U256Value.tuple words))
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
    (normal : evaluateHOLFiniteState source afterSender = (some (.returned returned),post)) :
    ∃ (middle finish : PanSemStateFiniteExact 64 Guest.HostMemory) (lt : BitVec 64) (newNb : Input.RlpWrite.U256Value.Words)
      (destroyed found : Bool) (iterations nextCursor : Nat) (next : ι → TableFamily.Object) (nextEntries : Nat → Journal.Entry ι) (nextCount : Nat),
      iterations ≤ populationBound ∧ middle.locals = ((source.locals.update (ofString "lt",.val (.word lt))).update (ofString "s",.val (.word (BitVec.ofNat 64 cursor)))).update (ofString "nb",Input.RlpWrite.U256Value.tuple newNb) ∧
      AccountMutation.Result source middle cursor nextCursor cutoff protectedCursor objects next outer base cap count nextCount nextEntries accounts (accounts ++ [BitVec.ofNat 64 cursor])
        property (AccountValueExtension.added property accountWriter (BitVec.ofNat 64 cursor))
        (9 + commitPrice (objects writer).slots.length (objects outer).slots.length (objects accountWriter).slots.length destroyed found iterations) 3 (populationBound + iterations + 2) ∧
      evaluateHOLFiniteState middle recipient = (some (.returned returned),finish) ∧ emptyLocalsHOLFinite post = emptyLocalsHOLFinite finish := by
  classical
  obtain ⟨accountImage⟩ := registry.images account accountMember
  let oldWords := Input.RlpWrite.U256Value.memoryWords source (account + 8#64)
  let lt := U256LessThan.resultWord oldWords words
  have loadRead : evalHOLExact (toExact source) (.load Input.RlpWrite.U256Value.tupleShape (.op .add [localVar "s",.const 8#64])) = some (Input.RlpWrite.U256Value.tuple oldWords) := accountImage.balance_read_at source account "s" accountLocal
  have args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) (balanceArguments "s") =
      some [Input.RlpWrite.U256Value.tuple oldWords,Input.RlpWrite.U256Value.tuple words] := by
    rw [evalListHOLFinite,balanceArguments,evalListHOLExact,loadRead]
    simp [evalListHOLExact,evalHOLExact,localVar,toExact,amountLocal]
  obtain ⟨positive,inner,tailRun,scope⟩ := U256LessThan.success_prefix source post oldWords words "lt" (balanceArguments "s") afterCompare args (U256LessThan.original_code source.code installed) returned normal
  let ready := setVarHOLFinite (ofString "lt") (.val (.word lt)) {source with clock := source.clock - 1}
  have arithmetic : AccountMutation.Result source ready cursor cursor cutoff protectedCursor objects objects outer base cap count count entries accounts accounts property property 1 0 populationBound :=
    AccountMutation.control source cursor cutoff protectedCursor populationBound objects outer base cap count entries accounts property family image zone countBound protect population environment registry values savedValues counter 1 positive
      (source.locals.update (ofString "lt",.val (.word lt)))
  have readyAddress : ready.locals.lookup (ofString "sender") = some (.val (.word address)) := by
    simpa [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "lt" ≠ ofString "sender" by decide] using addressLocal
  have readyAccount : ready.locals.lookup (ofString "s") = some (.val (.word account)) := by
    simpa [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "lt" ≠ ofString "s" by decide] using accountLocal
  have readyAmount : ready.locals.lookup (ofString "amount") = some (Input.RlpWrite.U256Value.tuple words) := by
    simpa [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "lt" ≠ ofString "amount" by decide] using amountLocal
  have copyRun := guard_safe.normal_continue ready inner (.seq (copyAccount "s") afterCopy) returned tailRun
  obtain ⟨middle,finish,newNb,destroyed,found,iterations,nextCursor,next,nextEntries,nextCount,visits,locals,result,recipientRun,postFrame⟩ := sender_copy_prefix ready inner address account emptyHash scratch transaction
    cursor cutoff protectedCursor populationBound objects writer outer accountWriter base cap count entries population arithmetic.family arithmetic.image arithmetic.zone countBound arithmetic.environment installed
    accounts arithmetic.registry property arithmetic.values owned accountOwned arithmetic.savedValues writerKind outerKind accountKind differentOuter addressArena scratchArena floors scratchBelow small journalAbove
    accountMember protect words readyAddress readyAccount readyAmount emptyGlobal emptyArena innerReferences scratchGlobal transactionGlobal tableMapped tableStored tableAbove tableAway tableBefore tableOutside
    outerMapped outerStored outerBefore outerOutside outerAway accountMapped accountStored accountAbove accountBefore accountOutside accountAway accountApart journal capacity counter returned copyRun
  refine ⟨middle,finish,lt,newNb,destroyed,found,iterations,nextCursor,next,nextEntries,nextCount,visits,locals,?_,recipientRun,?_⟩
  · simpa only [← Nat.add_assoc,Nat.reduceAdd,Nat.zero_add] using arithmetic.trans result
  · rw [scope]
    exact postFrame

end InitECandidate.Solver.Mpt.AccountEtherMove

#print axioms InitECandidate.Solver.Mpt.AccountEtherMove.sender_compare_prefix
