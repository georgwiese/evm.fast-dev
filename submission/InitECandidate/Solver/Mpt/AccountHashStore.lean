import InitECandidate.Solver.Mpt.AccountReferenceStore
import InitECandidate.Solver.Mpt.AccountMutationResult
import InitECandidate.Solver.Mpt.AccountMutationWrites

namespace InitECandidate.Solver.Mpt.AccountMutation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix MutableTable GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def hashField (name : String) (expression : ExpHOL 64) : ProgHOL 64 :=
  .store (.op .add [localVar name,.const 48#64]) expression

theorem hash_field {ι : Type} [Fintype ι]
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor cutoff protectedCursor population : Nat)
    (objects : ι → TableFamily.Object) (outer : ι) (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (accounts : List (BitVec 64)) (property : ι → BitVec 64 → Prop)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap)
    (populations : ∀ index,(objects index).slots.length ≤ population) (environment : WarmKeys.Environment source)
    (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (values : TableFamily.ValuesHave source objects property) (savedValues : Journal.EntryValues entries count property)
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (account : BitVec 64) (member : account ∈ accounts) (protectObject : protectedCursor ≤ account.toNat)
    (apart : account.toNat + 56 ≤ base ∨ base + 32 * cap ≤ account.toNat)
    (emptyHash : BitVec 64) (hashArena : AllocatedBytes.Arena emptyHash 32)
    (expression : ExpHOL 64) (hashRead : eval source expression = some (.val (.word emptyHash)))
    (name : String) (binding : source.locals.lookup (ofString name) = some (.val (.word account))) :
    let writes := [(account + 48#64,emptyHash)]
    let target := {source with memory := WordWrites.write source.memory writes}
    evaluateHOLFiniteState source (hashField name expression) = (none,target) ∧
      Rlp.Slices.Window source target account.toNat (account.toNat + 56) ∧
      Result source target cursor cursor cutoff protectedCursor objects objects outer base cap count count entries accounts accounts property property 0 0 population := by
  obtain ⟨accountImage⟩ := registry.images account member
  have destination (offset : BitVec 64) : eval source (.op .add [localVar name,.const offset]) = some (.val (.word (account + offset))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,binding,valueIsWord,valueWord,wordOpHOL,wordOp]
  obtain ⟨hashRun,nextFamily,nextRegistry,nextValues⟩ := registry.reference_store source cutoff cursor objects accounts family property values account member 48 (Or.inr rfl)
    _ expression emptyHash hashArena (destination 48#64) hashRead
  let writes := [(account + 48#64,emptyHash)]
  let target := {source with memory := WordWrites.write source.memory writes}
  have contained : ∀ entry ∈ writes,∃ offset : Nat,offset < 56 ∧ entry.1 = account + BitVec.ofNat 64 offset := by
    intro entry found
    have same : entry = (account + 48#64,emptyHash) := by simpa [writes] using found
    subst entry
    exact ⟨48,by decide,rfl⟩
  have window := AccountDecode.object_writes_window source account accountImage writes contained
  have nextImage := AccountDecode.journal_after_object_writes source objects base cap count cursor entries image zone countBound account accountImage apart writes contained
  have execute : evaluateHOLFiniteState source (hashField name expression) = (none,target) := hashRun
  have objectBefore := registry.before account member
  refine ⟨execute,window,?_⟩
  exact {
    clockForward := Nat.le_refl _
    cursorForward := Nat.le_refl _
    protectedBefore := by omega
    countForward := Nat.le_refl _
    countBound := countBound
    appends := by omega
    family := nextFamily
    image := nextImage
    zone := zone
    work := by simp [target]
    populations := populations
    code := rfl
    oracle := rfl
    environment := environment.of_fields rfl rfl rfl
    globals := fun _ _ _ => rfl
    values := nextValues
    savedValues := savedValues
    registry := nextRegistry
    extension := AccountDecode.Registry.Extension.refl accounts cursor
    effect := by simpa only [Nat.sub_self] using Journal.CounterEffect.unchanged source target rfl
    metadata := TableFamily.Metadata.refl objects
    frame := fun query _ before outside _ => ⟨outside,window query (Or.inl (Nat.lt_of_lt_of_le before protectObject))⟩
    counter := counter
    propertyIncluded := fun _ _ owned => owned
    outerValues := fun _ => Iff.rfl
    readerKnown := fun _ _ known => known }

end InitECandidate.Solver.Mpt.AccountMutation

#print axioms InitECandidate.Solver.Mpt.AccountMutation.hash_field
