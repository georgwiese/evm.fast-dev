import InitECandidate.Solver.Mpt.AccountEtherMoveSenderSub
import InitECandidate.Solver.Mpt.AccountCopyMutationResult
import InitECandidate.Solver.Mpt.AccountMutationFields

namespace InitECandidate.Solver.Mpt.AccountEtherMove
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget AccountBalanceSet

theorem sender_copy_prefix {ι : Type} [Fintype ι] [DecidableEq ι]
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
    (normal : evaluateHOLFiniteState source (.seq (copyAccount "s") afterCopy) = (some (.returned returned),post)) :
    ∃ (middle finish : PanSemStateFiniteExact 64 Guest.HostMemory) (newNb : Input.RlpWrite.U256Value.Words)
      (destroyed found : Bool) (iterations nextCursor : Nat) (next : ι → TableFamily.Object) (nextEntries : Nat → Journal.Entry ι) (nextCount : Nat),
      iterations ≤ populationBound ∧ middle.locals = (source.locals.update (ofString "s",.val (.word (BitVec.ofNat 64 cursor)))).update (ofString "nb",Input.RlpWrite.U256Value.tuple newNb) ∧
      AccountMutation.Result source middle cursor nextCursor cutoff protectedCursor objects next outer base cap count nextCount nextEntries accounts (accounts ++ [BitVec.ofNat 64 cursor])
        property (AccountValueExtension.added property accountWriter (BitVec.ofNat 64 cursor))
        (8 + commitPrice (objects writer).slots.length (objects outer).slots.length (objects accountWriter).slots.length destroyed found iterations) 3 (populationBound + iterations + 2) ∧
      evaluateHOLFiniteState middle recipient = (some (.returned returned),finish) ∧ emptyLocalsHOLFinite post = emptyLocalsHOLFinite finish := by
  have safe : Input.LocalPrefix (ofString "sender") (copyAccount "s") := .call (some (ofString "s")) _ _ (by
    intro name same
    have equal : name = ofString "s" := Option.some.inj same.symm
    rw [equal]
    decide)
  obtain ⟨copied,copyRun,tailRun,keepSender⟩ := safe.normal_continue source post afterCopy returned normal
  obtain ⟨copyLocals,window,copyResult⟩ := AccountMutation.copy source copied cursor cutoff protectedCursor populationBound objects accountWriter outer differentOuter base cap count entries accounts property
    family image zone countBound protect journalAbove population environment installed registry values savedValues counter account accountMember "s" accountLocal copyRun
  let heap := BitVec.ofNat 64 cursor
  let nextProperty := AccountValueExtension.added property accountWriter heap
  have heapNumber : heap.toNat = cursor := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := (family.tables writer).bounded; omega)]
  have copyAddress : copied.locals.lookup (ofString "sender") = some (.val (.word address)) := keepSender.trans addressLocal
  have copyAccount : copied.locals.lookup (ofString "s") = some (.val (.word heap)) := by
    rw [copyLocals]
    simp [heap,HolFiniteMapExact.update,FUPDATE]
  have copyAmount : copied.locals.lookup (ofString "amount") = some (Input.RlpWrite.U256Value.tuple words) := by
    rw [copyLocals]
    simpa [HolFiniteMapExact.update,FUPDATE,show ofString "s" ≠ ofString "amount" by decide] using amountLocal
  have copyInstalled : Input.OriginalCode.Installed copied.code := by rw [copyResult.code]; exact installed
  have copyApart := copyResult.extension.journal_apart accountApart zone.earlier
  have mapped (query : BitVec 64) (mapping : source.memaddrs query) : copied.memaddrs query := by
    rw [copyResult.environment.domain,← environment.domain]
    exact mapping
  have memory (query : BitVec 64) (before : query.toNat < protectedCursor) : copied.memory query = source.memory query := window query (Or.inl (Nat.lt_of_lt_of_le before protect))
  obtain ⟨middle,finish,newNb,destroyed,found,iterations,nextCursor,next,nextEntries,nextCount,visits,locals,result,recipientRun,scope⟩ := sender_sub_prefix copied post address heap emptyHash scratch transaction
    (cursor + 56) cutoff protectedCursor populationBound objects writer outer accountWriter base cap count entries population copyResult.family copyResult.image copyResult.zone countBound copyResult.environment copyInstalled
    (accounts ++ [heap]) copyResult.registry nextProperty copyResult.values (Or.inl owned) (Or.inl accountOwned) (Or.inr ⟨rfl,rfl⟩) copyResult.savedValues
    writerKind outerKind accountKind differentOuter addressArena scratchArena floors scratchBelow small journalAbove (by simp) (by rw [heapNumber]; exact protect) words copyAddress copyAccount copyAmount
    ((copyResult.globals (ofString "empty_code_hash") (by decide) (by decide)).trans emptyGlobal) emptyArena (copyResult.references innerReferences)
    ((copyResult.globals (ofString "sk_buf") (by decide) (by decide)).trans scratchGlobal) ((copyResult.globals (ofString "ts") (by decide) (by decide)).trans transactionGlobal)
    (mapped _ tableMapped) ((memory _ tableBefore).trans tableStored) tableAbove tableAway tableBefore tableOutside
    (mapped _ outerMapped) ((memory _ outerBefore).trans outerStored) outerBefore outerOutside outerAway
    (mapped _ accountMapped) ((memory _ accountBefore).trans accountStored) accountAbove accountBefore accountOutside accountAway copyApart
    ((copyResult.globals (ofString "journal") (by decide) (by decide)).trans journal) ((copyResult.globals (ofString "journal_cap") (by decide) (by decide)).trans capacity) copyResult.counter returned tailRun
  have total := copyResult.trans result
  refine ⟨middle,finish,newNb,destroyed,found,iterations,nextCursor,next,nextEntries,nextCount,visits,?_,?_,recipientRun,?_⟩
  · rw [locals,copyLocals]
  · simpa only [← Nat.add_assoc,Nat.reduceAdd,Nat.zero_add] using total
  · rw [scope]
    rfl

end InitECandidate.Solver.Mpt.AccountEtherMove

#print axioms InitECandidate.Solver.Mpt.AccountEtherMove.sender_copy_prefix
