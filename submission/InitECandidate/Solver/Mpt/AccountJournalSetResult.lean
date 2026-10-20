import InitECandidate.Solver.GasBudget.JournalAppendSetRegistered
import InitECandidate.Solver.Mpt.AccountMutationResult
import InitECandidate.Solver.MutableTable.FamilyPotential

namespace InitECandidate.Solver.Mpt.AccountMutation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix MutableTable GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem journal_set {ι : Type} [Fintype ι] [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor protectedCursor population : Nat) (objects : ι → TableFamily.Object) (writer outer : ι)
    (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap) (environment : WarmKeys.Environment source)
    (cutoff : Nat) (accounts : List (BitVec 64)) (registry : Mpt.AccountDecode.Registry source cutoff cursor objects accounts)
    (accountApart : ∀ account,account∈accounts → account.toNat+56≤base ∨ base+32*cap≤account.toNat)
    (before : protectedCursor ≤ cursor) (populations : ∀ index,(objects index).slots.length ≤ population)
    (query value : BitVec 64)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (owned : property writer value)
    (savedValues : Journal.EntryValues entries count property)
    (queryFits : query.toNat + KeyHash.keySize (objects writer).kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize (objects writer).kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (getCode : source.code.lookup (ofString "htab_get") = some (Get.formals, Get.body, Get.pairShape))
    (code : source.code.lookup (ofString "jset") = some (TableCall.formals, Journal.Append.setBody, .one))
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (capacity : source.globals.lookup (ofString "journal_cap") = some (.val (.word (BitVec.ofNat 64 cap))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (TableCall.values (objects writer).pointer query value))
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "jset") arguments) = (none, post)) :
    ∃ nextCursor nextEntries nextObjects,
      post.locals = source.locals ∧ Journal.ProtectedFrame base cap cursor objects nextObjects source post ∧
      Result source post cursor nextCursor cutoff protectedCursor objects nextObjects outer base cap count (count + 1) nextEntries accounts accounts property property
        (Journal.Append.setPrice (objects writer).kind (objects writer).slots.length + 1) 1 (population + 1) := by
  obtain ⟨room,paid,nextCursor,next,flag,oldValue,positive,funded,clock,forward,kind,binary,models,nextImage,nextZone,price,nextPopulation,nextCounter,locals,codes,nextEnvironment,globals,effect,frame,nextValues,nextSaved,nextRegistry,metadata⟩ :=
    Journal.Append.set_call_registered_values source post cursor objects writer base cap count entries family image zone countBound environment cutoff accounts registry accountApart query value property values owned savedValues
      queryFits queryMapped getCode code journal capacity counter arguments args normal
  have localPrice : paid + (objects writer).potential ≤ Journal.Append.setPrice (objects writer).kind (objects writer).slots.length + 1 + next.potential := by
    simpa only [TableFamily.Object.potential,kind] using price
  have familyPrice := TableFamily.amortized_update objects writer next paid _ localPrice
  have spent : source.clock - post.clock = paid := by rw [clock,Nat.sub_sub_self funded]
  refine ⟨nextCursor,Function.update entries count ⟨writer,BitVec.ofNat 64 cursor,flag,oldValue⟩,Function.update objects writer next,locals,frame,?_⟩
  exact {
    clockForward := by rw [clock]; exact Nat.sub_le _ _
    cursorForward := forward
    protectedBefore := before
    countForward := by omega
    countBound := by omega
    appends := by omega
    family := models
    image := nextImage
    zone := nextZone
    work := by rw [spent]; exact familyPrice
    populations := TableFamily.population_update objects writer next population populations nextPopulation
    code := codes
    oracle := Input.evaluation_oracle source post (.call (some (none,none)) (ofString "jset") arguments) none normal
    environment := nextEnvironment
    globals := globals
    values := nextValues
    savedValues := nextSaved
    registry := nextRegistry
    extension := AccountDecode.Registry.Extension.refl accounts cursor
    effect := by simpa only [Nat.add_sub_cancel_left] using effect
    metadata := metadata
    frame := fun query _ earlier outside away => frame.words query (Nat.lt_of_lt_of_le earlier before) outside away
    counter := nextCounter
    propertyIncluded := fun _ _ owned => owned
    outerValues := fun _ => Iff.rfl
    readerKnown := fun _ _ known => known }

end InitECandidate.Solver.Mpt.AccountMutation

#print axioms InitECandidate.Solver.Mpt.AccountMutation.journal_set
