import InitECandidate.Solver.Mpt.AccountEtherMoveSenderCommit
import InitECandidate.Solver.Mpt.AccountObjectReads
import InitECandidate.Solver.Mpt.AccountMutationControl

namespace InitECandidate.Solver.Mpt.AccountEtherMove
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget AccountBalanceSet

theorem sender_sub_prefix {ι : Type} [Fintype ι] [DecidableEq ι]
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
    (normal : evaluateHOLFiniteState source afterCopy = (some (.returned returned),post)) :
    ∃ (middle finish : PanSemStateFiniteExact 64 Guest.HostMemory) (newNb : Input.RlpWrite.U256Value.Words)
      (destroyed found : Bool) (iterations nextCursor : Nat) (next : ι → TableFamily.Object) (nextEntries : Nat → Journal.Entry ι) (nextCount : Nat),
      iterations ≤ populationBound ∧ middle.locals = source.locals.update (ofString "nb",Input.RlpWrite.U256Value.tuple newNb) ∧
      AccountMutation.Result source middle cursor nextCursor cutoff protectedCursor objects next outer base cap count nextCount nextEntries accounts accounts property property
        (1 + commitPrice (objects writer).slots.length (objects outer).slots.length (objects accountWriter).slots.length destroyed found iterations) 3 (populationBound + iterations + 2) ∧
      evaluateHOLFiniteState middle recipient = (some (.returned returned),finish) ∧ post = restore source "nb" finish := by
  classical
  obtain ⟨accountImage⟩ := registry.images account accountMember
  let oldWords := Input.RlpWrite.U256Value.memoryWords source (account + 8#64)
  let newWords := U256Sub.result oldWords words
  have loadRead : evalHOLExact (toExact source) (.load Input.RlpWrite.U256Value.tupleShape (.op .add [localVar "s",.const 8#64])) = some (Input.RlpWrite.U256Value.tuple oldWords) := accountImage.balance_read_at source account "s" accountLocal
  have args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) (balanceArguments "s") =
      some [Input.RlpWrite.U256Value.tuple oldWords,Input.RlpWrite.U256Value.tuple words] := by
    rw [evalListHOLFinite,balanceArguments,evalListHOLExact,loadRead]
    simp [evalListHOLExact,evalHOLExact,localVar,toExact,amountLocal]
  obtain ⟨positive,finish,tailRun,scope⟩ := U256Sub.success_prefix source post oldWords words "nb" (balanceArguments "s") senderCommit args (U256Sub.original_code source.code installed) returned normal
  let ready := setVarHOLFinite (ofString "nb") (Input.RlpWrite.U256Value.tuple newWords) {source with clock := source.clock - 1}
  have protect : protectedCursor ≤ cursor := by have current := registry.before account accountMember; omega
  have arithmetic : AccountMutation.Result source ready cursor cursor cutoff protectedCursor objects objects outer base cap count count entries accounts accounts property property 1 0 populationBound :=
    AccountMutation.control source cursor cutoff protectedCursor populationBound objects outer base cap count entries accounts property family image zone countBound protect population environment registry values savedValues counter 1 positive
      (source.locals.update (ofString "nb",Input.RlpWrite.U256Value.tuple newWords))
  have readyAddress : ready.locals.lookup (ofString "sender") = some (.val (.word address)) := by
    simpa [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "nb" ≠ ofString "sender" by decide] using addressLocal
  have readyAccount : ready.locals.lookup (ofString "s") = some (.val (.word account)) := by
    simpa [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "nb" ≠ ofString "s" by decide] using accountLocal
  have readyNb : ready.locals.lookup (ofString "nb") = some (Input.RlpWrite.U256Value.tuple newWords) := by
    simp [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  obtain ⟨middle,destroyed,found,iterations,nextCursor,next,nextEntries,nextCount,visits,locals,result,recipientRun⟩ := sender_commit_prefix ready finish address account emptyHash scratch transaction
    cursor cutoff protectedCursor populationBound objects writer outer accountWriter base cap count entries population arithmetic.family arithmetic.image arithmetic.zone countBound arithmetic.environment installed accounts arithmetic.registry property arithmetic.values owned accountOwned publishOwned arithmetic.savedValues
    writerKind outerKind accountKind differentOuter addressArena scratchArena floors scratchBelow small journalAbove accountMember protectedBefore newWords readyAddress readyAccount readyNb
    emptyGlobal emptyArena innerReferences scratchGlobal transactionGlobal tableMapped tableStored tableAbove tableAway tableBefore tableOutside outerMapped outerStored outerBefore outerOutside outerAway accountMapped accountStored accountAbove accountBefore accountOutside accountAway accountApart journal capacity counter returned tailRun
  exact ⟨middle,finish,newWords,destroyed,found,iterations,nextCursor,next,nextEntries,nextCount,visits,locals,arithmetic.trans result,recipientRun,scope⟩

end InitECandidate.Solver.Mpt.AccountEtherMove

#print axioms InitECandidate.Solver.Mpt.AccountEtherMove.sender_sub_prefix
