import InitECandidate.Solver.Mpt.AccountMutationComposition

namespace InitECandidate.Solver.Mpt.AccountMutation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix MutableTable GasBudget
open Flapjack.Basis.Pure.MlString

/-- Exact control-only endpoints from the checked arithmetic/call contracts
retain the complete current state model and contribute no journal append. -/
theorem control {ι : Type} [Fintype ι]
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor cutoff protectedCursor population : Nat)
    (objects : ι → TableFamily.Object) (outer : ι) (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (accounts : List (BitVec 64)) (property : ι → BitVec 64 → Prop)
    (family : TableFamily.Model source cursor objects) (image : Journal.Image source objects base count entries)
    (zone : Journal.Zone objects base cap cursor) (countBound : count ≤ cap) (before : protectedCursor ≤ cursor)
    (populations : ∀ index,(objects index).slots.length ≤ population)
    (environment : WarmKeys.Environment source) (registry : AccountDecode.Registry source cutoff cursor objects accounts)
    (values : TableFamily.ValuesHave source objects property) (savedValues : Journal.EntryValues entries count property)
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count))))
    (paid : Nat) (funded : paid ≤ source.clock) (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    Result source {source with clock := source.clock - paid,locals := locals} cursor cursor cutoff protectedCursor objects objects outer base cap count count entries
      accounts accounts property property paid 0 population := by
  let target := {source with clock := source.clock - paid,locals := locals}
  exact {
    clockForward := Nat.sub_le _ _
    cursorForward := Nat.le_refl _
    protectedBefore := before
    countForward := Nat.le_refl _
    countBound := countBound
    appends := by omega
    family := family.of_control rfl rfl rfl rfl
    image := image.transfer rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ _ => rfl) image.separate
    zone := zone
    work := by change source.clock - (source.clock - paid) + _ ≤ _; omega
    populations := populations
    code := rfl
    oracle := rfl
    environment := environment.of_fields rfl rfl rfl
    globals := fun _ _ _ => rfl
    values := values
    savedValues := savedValues
    registry := registry.framed source target cutoff cursor cursor objects objects accounts (TableFamily.PersistentFrame.of_memory cutoff cursor objects source target rfl) (Nat.le_refl _) rfl
    extension := AccountDecode.Registry.Extension.refl accounts cursor
    effect := by simpa only [Nat.sub_self] using Journal.CounterEffect.unchanged source target rfl
    metadata := TableFamily.Metadata.refl objects
    frame := fun _ _ _ outside _ => ⟨outside,rfl⟩
    counter := counter
    propertyIncluded := fun _ _ owned => owned
    outerValues := fun _ => Iff.rfl
    readerKnown := fun _ _ known => known }

end InitECandidate.Solver.Mpt.AccountMutation

#print axioms InitECandidate.Solver.Mpt.AccountMutation.control
