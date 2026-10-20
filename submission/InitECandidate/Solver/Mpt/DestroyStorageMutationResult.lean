import InitECandidate.Solver.Mpt.DestroyStorageCall
import InitECandidate.Solver.Mpt.AccountMutationResult
import InitECandidate.Solver.Mpt.AccountBalanceSetPrice

namespace InitECandidate.Solver.Mpt.DestroyStorage
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout GasBudget

def phasePrice (markers outers : Nat) (found : Bool) (iterations : Nat) : Nat :=
  Get.bodyPrice .account outers + 2 + (if found then loopPrice markers iterations + Journal.Append.deletePrice .account outers + 1 else 0)

theorem phase_price_mono (markers outers bound : Nat) (markerBound : markers ≤ bound) (outerBound : outers ≤ bound) (found : Bool) (iterations : Nat) :
    phasePrice markers outers found iterations ≤ phasePrice bound bound found iterations := by
  have get := AccountBalanceSet.get_price_mono .account outers bound outerBound
  have delete := AccountBalanceSet.delete_price_mono .account outers bound outerBound
  have loop := loop_price_mono markers bound iterations markerBound
  cases found <;> simp only [phasePrice,Bool.false_eq_true,↓reduceIte] <;> omega

theorem call_core {ι : Type} [Fintype ι] [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (address scratch transaction : BitVec 64)
    (cursor cutoff protectedCursor populationBound : Nat) (objects : ι → TableFamily.Object) (writer outer : ι)
    (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (protectedBefore : protectedCursor ≤ cursor) (population : ∀ index,(objects index).slots.length ≤ populationBound)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (accounts : List (BitVec 64)) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (owned : property writer 1#64) (savedValues : Journal.EntryValues entries count property)
    (writerKind : (objects writer).kind = .storage) (outerKind : (objects outer).kind = .account)
    (addressArena : AllocatedBytes.Arena address 20) (scratchArena : AllocatedBytes.Arena scratch 52)
    (floors : ∀ index, cutoff ≤ (objects index).floor) (scratchBelow : scratch.toNat + 52 ≤ cutoff)
    (small : cutoff < 2^64) (journalAbove : cutoff ≤ base)
    (innerReferences : ∀ item, property outer item → ∃ reader, (objects reader).pointer = item ∧ (objects reader).kind = .word)
    (scratchGlobal : source.globals.lookup (ofString "sk_buf") = some (.val (.word scratch)))
    (transactionGlobal : source.globals.lookup (ofString "ts") = some (.val (.word transaction)))
    (tableMapped : source.memaddrs (transaction + 24#64))
    (tableStored : source.memory (transaction + 24#64) = .word (objects writer).pointer)
    (tableAbove : cutoff ≤ (transaction + 24#64).toNat)
    (tableBefore : (transaction + 24#64).toNat < cursor) (tableOutside : TableFamily.Outside objects (transaction + 24#64))
    (outerMapped : source.memaddrs (transaction + 32#64))
    (outerStored : source.memory (transaction + 32#64) = .word (objects outer).pointer)
    (accountApart : ∀ account,account ∈ accounts → account.toNat + 56 ≤ base ∨ base + 32 * cap ≤ account.toNat)
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) expressions = some [.val (.word address)])
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "destroy_storage") expressions) = (none,post)) :
    ∃ (found : Bool) (iterations nextCursor : Nat) (next : ι → TableFamily.Object) (nextEntries : Nat → Journal.Entry ι) (nextCount : Nat),
      iterations ≤ populationBound ∧ post.locals = source.locals ∧
      AccountMutation.Result source post cursor nextCursor cutoff protectedCursor objects next outer base cap count nextCount nextEntries accounts accounts property property
        (phasePrice (objects writer).slots.length (objects outer).slots.length found iterations) 1 (populationBound + iterations) := by
  obtain ⟨found,iterations,paid,nextCursor,next,nextEntries,added,positive,funded,clock,forward,addedBound,capacityBound,models,nextImage,nextZone,price,locals,codes,nextEnvironment,globals,nextValues,nextSaved,nextRegistry,effect,metadata,frame,others,branch,nextCounter,outerPlan,markerPopulation,outerPopulation⟩ := call_normal source post address scratch transaction
    cursor cutoff objects writer outer base cap count entries family image zone countBound environment installed accounts registry property values owned savedValues writerKind outerKind addressArena scratchArena floors scratchBelow small journalAbove innerReferences scratchGlobal transactionGlobal
    tableMapped tableStored tableAbove tableBefore tableOutside outerMapped outerStored accountApart journal capacity counter expressions args normal
  have different : writer ≠ outer := by
    intro same
    rw [same,outerKind] at writerKind
    cases writerKind
  have otherPotentials (index : ι) (notWriter : index ≠ writer) (notOuter : index ≠ outer) : (next index).potential = (objects index).potential := by
    rw [others index notWriter notOuter]
  have localPrice : paid + (objects writer).potential + (objects outer).potential ≤
      phasePrice (objects writer).slots.length (objects outer).slots.length found iterations + (next writer).potential + (next outer).potential := by
    simp only [TableFamily.Object.potential,metadata.kinds writer,metadata.kinds outer,outerPlan,phasePrice]
    rw [outerKind] at price
    omega
  have familyPrice := TableFamily.amortized_two objects next writer outer different otherPotentials paid _ localPrice
  have visits : iterations ≤ populationBound := by
    rcases branch with absent | ⟨_,index,_,visited⟩
    · have zero := absent.2.1
      omega
    · rw [visited]
      exact population index
  have populations (index : ι) : (next index).slots.length ≤ populationBound + iterations := by
    have old := population index
    by_cases atMarker : index = writer
    · subst index
      omega
    · by_cases atOuter : index = outer
      · subst index
        omega
      · rw [others index atMarker atOuter]
        omega
  have spent : source.clock - post.clock = paid := by rw [clock,Nat.sub_sub_self funded]
  have delta : count + added - count = added := by omega
  refine ⟨found,iterations,nextCursor,next,nextEntries,count + added,visits,locals,?_⟩
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
    oracle := Input.evaluation_oracle source post (.call (some (none,none)) (ofString "destroy_storage") expressions) none normal
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

end InitECandidate.Solver.Mpt.DestroyStorage

#print axioms InitECandidate.Solver.Mpt.DestroyStorage.phase_price_mono
#print axioms InitECandidate.Solver.Mpt.DestroyStorage.call_core
