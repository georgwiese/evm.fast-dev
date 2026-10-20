import InitECandidate.Solver.Mpt.AccountClearProgram
import InitECandidate.Solver.Mpt.AccountCommitMutationResult
import InitECandidate.Solver.Mpt.AccountMutationAgreement

namespace InitECandidate.Solver.Mpt.AccountClear
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

theorem after_copy_normal {ι : Type} [Fintype ι] [DecidableEq ι]
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
    (accountMember : account ∈ accounts)
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
    (addressLocal : source.locals.lookup (ofString "addr") = some (.val (.word address)))
    (accountLocal : source.locals.lookup (ofString "a") = some (.val (.word account)))
    (protectObject : protectedCursor ≤ account.toNat)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterCopy = (some (.returned returned),post)) :
    returned = .val (.word 0#64) ∧ ∃ (destroyed found : Bool) (iterations nextCursor : Nat)
      (next : ι → TableFamily.Object) (nextEntries : Nat → Journal.Entry ι) (nextCount : Nat),
      iterations ≤ populationBound ∧ AccountMutation.Result source post cursor nextCursor cutoff protectedCursor objects next outer base cap count nextCount nextEntries accounts accounts property property
        (AccountBalanceSet.commitPrice (objects writer).slots.length (objects outer).slots.length (objects accountWriter).slots.length destroyed found iterations) 3 (populationBound + iterations + 2) := by
  obtain ⟨resetRun,window,resetData⟩ := AccountMutation.reset_fields source cursor cutoff protectedCursor populationBound objects outer base cap count entries accounts property family image zone countBound population environment registry values savedValues counter
    account accountMember protectObject (accountApart account accountMember) emptyHash emptyArena emptyGlobal "a" accountLocal
  let writes := [(account + 0#64,0#64),(account + 48#64,emptyHash)]
  let written := {source with memory := WordWrites.write source.memory writes}
  rw [after_copy_execute source] at normal
  have tailRun : evaluateHOLFiniteState written (.seq commitCall (.return (.const 0#64))) = (some (.returned returned),post) :=
    (StateSteps.next_sequence source written (AccountMutation.resetFields "a") (.seq commitCall (.return (.const 0#64))) resetRun (Nat.le_refl _)).symm.trans normal
  have safe : Input.LocalPrefix (ofString "addr") commitCall := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨mutated,commitRun,returnRun,keepAddress⟩ := safe.normal_continue written post (.return (.const 0#64)) returned tailRun
  have args : evalListHOLFinite written (h := fun query => Classical.propDecidable (written.memaddrs query)) [localVar "addr",localVar "a"] = some (AccountSet.values address account) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,show written.locals = source.locals from rfl,addressLocal,accountLocal,AccountSet.values]
  have storedTable : written.memory (transaction + 24#64) = .word (objects writer).pointer :=
    window (transaction + 24#64) (Or.inl (by omega)) |>.trans tableStored
  have storedOuter : written.memory (transaction + 32#64) = .word (objects outer).pointer :=
    window (transaction + 32#64) (Or.inl (by omega)) |>.trans outerStored
  have storedAccount : written.memory (transaction + 16#64) = .word (objects accountWriter).pointer :=
    window (transaction + 16#64) (Or.inl (by omega)) |>.trans accountStored
  obtain ⟨destroyed,found,iterations,nextCursor,next,nextEntries,nextCount,visits,locals,commitData⟩ := AccountCommit.call_core written mutated address account emptyHash scratch transaction
    cursor cutoff protectedCursor populationBound objects writer outer accountWriter base cap count entries resetData.protectedBefore population resetData.family resetData.image resetData.zone countBound resetData.environment installed accounts resetData.registry property resetData.values owned accountOwned publishOwned resetData.savedValues
    writerKind outerKind accountKind differentOuter addressArena scratchArena floors scratchBelow small journalAbove accountMember emptyGlobal emptyArena innerReferences scratchGlobal transactionGlobal tableMapped storedTable tableAbove tableAway (Nat.lt_of_lt_of_le tableBefore resetData.protectedBefore) tableOutside
    outerMapped storedOuter (Nat.lt_of_lt_of_le outerBefore resetData.protectedBefore) outerOutside outerAway accountMapped storedAccount accountAbove (Nat.lt_of_lt_of_le accountBefore resetData.protectedBefore) accountOutside accountAway accountApart journal capacity counter _ args commitRun
  have returnedInfo := Input.return_normal mutated post (.const 0#64) returned returnRun
  have answerEq : returned = .val (.word 0#64) := Option.some.inj (returnedInfo.1.symm.trans rfl)
  rw [returnedInfo.2]
  refine ⟨answerEq,destroyed,found,iterations,nextCursor,next,nextEntries,nextCount,visits,?_⟩
  simpa only [Nat.zero_add] using (resetData.trans commitData).local_agreement (by rfl)

end InitECandidate.Solver.Mpt.AccountClear

#print axioms InitECandidate.Solver.Mpt.AccountClear.after_copy_normal
