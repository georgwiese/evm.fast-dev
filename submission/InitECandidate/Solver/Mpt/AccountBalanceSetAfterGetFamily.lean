import InitECandidate.Solver.Mpt.AccountBalanceSetResult

namespace InitECandidate.Solver.Mpt.AccountBalanceSet
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

theorem after_get_family {ι : Type} [Fintype ι] [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (address account emptyHash scratch transaction : BitVec 64)
    (cursor cutoff populationBound : Nat) (objects : ι → TableFamily.Object) (writer outer accountWriter : ι)
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
    (accountMember : account ∈ accounts)
    (words : Input.RlpWrite.U256Value.Words)
    (addressLocal : source.locals.lookup (ofString "addr") = some (.val (.word address)))
    (accountLocal : source.locals.lookup (ofString "a") = some (.val (.word account)))
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
    (tableBefore : (transaction + 24#64).toNat < cursor) (tableOutside : TableFamily.Outside objects (transaction + 24#64))
    (outerMapped : source.memaddrs (transaction + 32#64))
    (outerStored : source.memory (transaction + 32#64) = .word (objects outer).pointer)
    (outerBefore : (transaction + 32#64).toNat < cursor)
    (outerOutside : TableFamily.Outside objects (transaction + 32#64)) (outerAway : Journal.Away base cap (transaction + 32#64))
    (accountMapped : source.memaddrs (transaction + 16#64))
    (accountStored : source.memory (transaction + 16#64) = .word (objects accountWriter).pointer)
    (accountAbove : cutoff ≤ (transaction + 16#64).toNat) (accountBefore : (transaction + 16#64).toNat < cursor)
    (accountOutside : TableFamily.Outside objects (transaction + 16#64)) (accountAway : Journal.Away base cap (transaction + 16#64))
    (accountApart : ∀ account,account ∈ accounts → account.toNat + 56 ≤ base ∨ base + 32 * cap ≤ account.toNat)
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterGet = (some (.returned returned),post)) :
    returned = .val (.word 0#64) ∧ Result source post cursor cutoff populationBound objects accountWriter base cap count accounts property
      (suffixPrice (objects writer).slots.length (objects outer).slots.length (objects accountWriter).slots.length) := by
  obtain ⟨answerEq,empty,destroyed,found,iterations,paid,nextCursor,next,nextEntries,added,positive,funded,clock,forward,addedPositive,addedBound,capacityBound,models,nextImage,nextZone,price,codes,nextEnvironment,globals,
    finalValues,finalSaved,finalRegistry,extension,effect,metadata,frame,others,branch,nextCounter,decision,binary,appends,outerPlan⟩ := after_get_normal source post address account emptyHash scratch transaction cursor cutoff objects writer outer accountWriter
      base cap count entries family image zone countBound environment installed accounts registry property values owned accountOwned savedValues
      writerKind outerKind accountKind differentOuter addressArena scratchArena floors scratchBelow small journalAbove accountMember words addressLocal accountLocal amountLocal
      emptyGlobal emptyArena innerReferences scratchGlobal transactionGlobal tableMapped tableStored tableAbove tableAway tableBefore tableOutside
      outerMapped outerStored outerBefore outerOutside outerAway accountMapped accountStored accountAbove accountBefore accountOutside accountAway accountApart journal capacity counter returned normal
  have different : writer ≠ accountWriter := by
    intro same
    rw [same,accountKind] at writerKind
    cases writerKind
  have otherPotentials (index : ι) (notWriter : index ≠ writer) (notAccount : index ≠ accountWriter) :
      (next index).potential = (objects index).potential := by
    by_cases atOuter : index = outer
    · subst index
      simp only [TableFamily.Object.potential,metadata.kinds outer,outerPlan]
    · rw [others index notWriter atOuter notAccount]
  have localPrice : paid + (objects writer).potential + (objects accountWriter).potential ≤
      suffixPrice (objects writer).slots.length (objects outer).slots.length (objects accountWriter).slots.length destroyed found iterations +
        (next writer).potential + (next accountWriter).potential := by
    simpa only [TableFamily.Object.potential,suffixPrice,writerKind,outerKind,accountKind,metadata.kinds writer,metadata.kinds accountWriter] using price
  have familyPrice := TableFamily.amortized_two objects next writer accountWriter different otherPotentials paid _ localPrice
  have visits : iterations ≤ populationBound := by
    rcases branch with ⟨_,zero⟩ | ⟨_,index,_,visited⟩
    · omega
    · rw [visited]
      exact population index
  exact ⟨answerEq,cursor,paid,nextCursor,next,nextEntries,accounts ++ [BitVec.ofNat 64 cursor],added,destroyed,found,iterations,Nat.le_refl _,extension,
    funded,clock,forward,addedPositive,addedBound,capacityBound,models,nextImage,nextZone,familyPrice,codes,nextEnvironment,globals,finalValues,finalSaved,finalRegistry,effect,metadata,frame,nextCounter,appends,visits⟩

end InitECandidate.Solver.Mpt.AccountBalanceSet

#print axioms InitECandidate.Solver.Mpt.AccountBalanceSet.after_get_family
