import InitECandidate.Solver.Mpt.AccountCopyAssigned
import InitECandidate.Solver.Mpt.AccountMutationResult
import InitECandidate.Solver.GasBudget.JournalPersistentFrame

namespace InitECandidate.Solver.Mpt.AccountMutation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix MutableTable GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual assigned account copy publishes only its real registered
fresh address into the value predicate; all journal entries remain intact. -/
theorem copy {ι : Type} [Fintype ι] [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor cutoff protectedCursor population : Nat)
    (objects : ι → TableFamily.Object) (writer outer : ι) (different : writer ≠ outer) (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (accounts : List (BitVec 64)) (property : ι → BitVec 64 → Prop)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap) (before : protectedCursor ≤ cursor)
    (journalAbove : cutoff ≤ base) (populations : ∀ index,(objects index).slots.length ≤ population)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (values : TableFamily.ValuesHave source objects property) (savedValues : Journal.EntryValues entries count property)
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (account : BitVec 64) (member : account ∈ accounts) (name : String)
    (binding : source.locals.lookup (ofString name) = some (.val (.word account)))
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,ofString name),none)) (ofString "acct_copy") [localVar name]) = (none,post)) :
    post.locals = source.locals.update (ofString name,.val (.word (BitVec.ofNat 64 cursor))) ∧
    Rlp.Slices.Window source post cursor (cursor + 56) ∧
    Result source post cursor (cursor + 56) cutoff protectedCursor objects objects outer base cap count count entries accounts (accounts ++ [BitVec.ofNat 64 cursor])
      property (AccountValueExtension.added property writer (BitVec.ofNat 64 cursor)) 7 0 population := by
  let heap := BitVec.ofNat 64 cursor
  have table := family.tables writer
  have heapNumber : heap.toNat = cursor := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := table.bounded; omega)]
  have currentFamily : TableFamily.Model source heap.toNat objects := by rw [heapNumber]; exact family
  have currentRegistry : AccountDecode.Registry source cutoff heap.toNat objects accounts := by rw [heapNumber]; exact registry
  have args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) [localVar name] = some [.val (.word account)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,binding]
  obtain ⟨funded,room,clock,locals,codes,domain,endian,globals,freshImage,window,heapAfter,models,nextRegistry,nextValues,extension,frame⟩ :=
    AccountCopy.assigned_registered source post account heap cutoff objects accounts currentFamily currentRegistry property values member table.heap
      (by rw [heapNumber]; exact table.bounded) (by rw [heapNumber]; exact table.aligned) installed name [localVar name] binding args normal
  rw [heapNumber] at room heapAfter models nextRegistry extension frame window
  obtain ⟨nextImage,nextZone⟩ := Journal.image_zone_framed source post cursor (cursor + 56) cutoff base cap count objects objects entries image zone countBound (by omega) journalAbove frame (TableFamily.Metadata.refl objects) domain
  have widened := AccountValueExtension.live_values post objects property nextValues writer heap
  have widenedSaved := AccountValueExtension.saved_values entries count property savedValues writer heap
  refine ⟨locals,window,?_⟩
  refine {
    clockForward := by omega
    cursorForward := by omega
    protectedBefore := before
    countForward := Nat.le_refl _
    countBound := countBound
    appends := by omega
    family := models
    image := nextImage
    zone := nextZone
    work := by rw [clock]; omega
    populations := populations
    code := codes
    oracle := Input.evaluation_oracle source post (.call (some (some (.local,ofString name),none)) (ofString "acct_copy") [localVar name]) none normal
    environment := environment.of_fields codes domain endian
    globals := fun key notHeap _ => globals key notHeap
    values := widened
    savedValues := widenedSaved
    registry := nextRegistry
    extension := extension
    effect := by simpa only [Nat.sub_self] using Journal.CounterEffect.unchanged source post (globals (ofString "journal_n") (by decide))
    metadata := TableFamily.Metadata.refl objects
    frame := fun query above earlier outside _ => frame.words query above (Nat.lt_of_lt_of_le earlier before) outside
    counter := (globals (ofString "journal_n") (by decide)).trans counter
    propertyIncluded := fun _ _ owned => Or.inl owned
    outerValues := fun value => AccountValueExtension.other property writer outer heap value different.symm
    readerKnown := ?_ }
  intro index _ known value owned
  rcases owned with old | ⟨_,rfl⟩
  · exact extension.known value (known value old)
  · exact Or.inr (by simp)

end InitECandidate.Solver.Mpt.AccountMutation

#print axioms InitECandidate.Solver.Mpt.AccountMutation.copy
