import InitECandidate.Solver.Mpt.AccountCommitCall
import InitECandidate.Solver.Mpt.AccountBalanceMutationFamily
import InitECandidate.Solver.Mpt.AccountMutationResult

namespace InitECandidate.Solver.Mpt.AccountCommit
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

theorem call_core {ι : Type} [Fintype ι] [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (address account emptyHash scratch transaction : BitVec 64)
    (cursor cutoff protectedCursor populationBound : Nat) (objects : ι → TableFamily.Object) (writer outer accountWriter : ι)
    (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (protectedBefore : protectedCursor ≤ cursor) (population : ∀ index,(objects index).slots.length ≤ populationBound)
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
    (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) expressions = some (AccountSet.values address account))
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "modify_state_commit") expressions) = (none,post)) :
    ∃ (destroyed found : Bool) (iterations nextCursor : Nat) (next : ι → TableFamily.Object) (nextEntries : Nat → Journal.Entry ι) (nextCount : Nat),
      iterations ≤ populationBound ∧ post.locals = source.locals ∧
      AccountMutation.Result source post cursor nextCursor cutoff protectedCursor objects next outer base cap count nextCount nextEntries accounts accounts property property
        (AccountBalanceSet.commitPrice (objects writer).slots.length (objects outer).slots.length (objects accountWriter).slots.length destroyed found iterations) 3 (populationBound + iterations + 2) := by
  obtain ⟨empty,destroyed,found,iterations,paid,nextCursor,next,nextEntries,added,positive,funded,clock,forward,addedPositive,addedBound,capacityBound,models,nextImage,nextZone,price,locals,codes,nextEnvironment,globals,
    nextValues,nextSaved,nextRegistry,effect,metadata,frame,others,branch,nextCounter,decision,binary,appends,outerPlan,markerPopulation,outerPopulation,accountPopulation⟩ := call_normal source post address account emptyHash scratch transaction
    cursor cutoff objects writer outer accountWriter base cap count entries family image zone countBound environment installed accounts registry property values owned accountOwned publishOwned savedValues
    writerKind outerKind accountKind differentOuter addressArena scratchArena floors scratchBelow small journalAbove accountMember emptyGlobal emptyArena innerReferences scratchGlobal transactionGlobal tableMapped tableStored tableAbove tableAway tableBefore tableOutside
    outerMapped outerStored outerBefore outerOutside outerAway accountMapped accountStored accountAbove accountBefore accountOutside accountAway accountApart journal capacity counter expressions args normal
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
      AccountBalanceSet.commitPrice (objects writer).slots.length (objects outer).slots.length (objects accountWriter).slots.length destroyed found iterations + (next writer).potential + (next accountWriter).potential := by
    simp only [TableFamily.Object.potential,AccountBalanceSet.commitPrice,AccountBalanceSet.suffixPrice,writerKind,outerKind,accountKind,metadata.kinds writer,metadata.kinds accountWriter]
    simp only [writerKind,outerKind,accountKind] at price
    omega
  have familyPrice := TableFamily.amortized_two objects next writer accountWriter different otherPotentials paid _ localPrice
  have visits : iterations ≤ populationBound := by
    rcases branch with ⟨_,zero⟩ | ⟨_,index,_,visited⟩
    · omega
    · rw [visited]
      exact population index
  have populations (index : ι) : (next index).slots.length ≤ populationBound + iterations + 2 := by
    have old := population index
    by_cases atMarker : index = writer
    · subst index
      omega
    · by_cases atAccount : index = accountWriter
      · subst index
        omega
      · by_cases atOuter : index = outer
        · subst index
          omega
        · rw [others index atMarker atOuter atAccount]
          omega
  have spent : source.clock - post.clock = paid := by rw [clock,Nat.sub_sub_self funded]
  have delta : count + added - count = added := by omega
  refine ⟨destroyed,found,iterations,nextCursor,next,nextEntries,count + added,visits,locals,?_⟩
  exact {
    clockForward := by rw [clock]; exact Nat.sub_le _ _
    cursorForward := forward
    protectedBefore := protectedBefore
    countForward := by omega
    countBound := capacityBound
    appends := by omega
    family := models
    image := nextImage
    zone := nextZone
    work := by rw [spent]; exact familyPrice
    populations := populations
    code := codes
    oracle := Input.evaluation_oracle source post (.call (some (none,none)) (ofString "modify_state_commit") expressions) none normal
    environment := nextEnvironment
    globals := globals
    values := nextValues
    savedValues := nextSaved
    registry := nextRegistry
    extension := AccountDecode.Registry.Extension.refl accounts cursor
    effect := by rw [delta]; exact effect
    metadata := metadata
    frame := fun query above before outside away => frame query above (Nat.lt_of_lt_of_le before protectedBefore) outside away
    counter := nextCounter
    propertyIncluded := fun _ _ owned => owned
    outerValues := fun _ => Iff.rfl
    readerKnown := fun _ _ known => known }

end InitECandidate.Solver.Mpt.AccountCommit

#print axioms InitECandidate.Solver.Mpt.AccountCommit.call_core
