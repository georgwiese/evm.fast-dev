import InitECandidate.Solver.Mpt.AccountMutationResult
import InitECandidate.Solver.GasBudget.JournalPersistentFrame

namespace InitECandidate.Solver.Mpt.AccountMutation
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable GasBudget
open Flapjack.Basis.Pure.MlString

/-- A reached account-cache/provider prefix contributes its real family
potential allowance, registry extension and unchanged journal reservation. -/
theorem heap_prefix {ι : Type} [Fintype ι]
    (source ready : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor readyCursor cutoff protectedCursor population : Nat)
    (objects next : ι → TableFamily.Object) (outer : ι) (base cap count : Nat) (entries : Nat → Journal.Entry ι)
    (accounts nextAccounts : List (BitVec 64)) (property : ι → BitVec 64 → Prop)
    (paid price : Nat) (funded : paid ≤ source.clock) (clock : ready.clock = source.clock - paid)
    (forward : cursor ≤ readyCursor) (before : protectedCursor ≤ cursor)
    (bound : paid + TableFamily.potential objects ≤ price + TableFamily.potential next)
    (models : TableFamily.Model ready readyCursor next) (populations : ∀ index,(next index).slots.length ≤ population)
    (image : Journal.Image source objects base count entries) (zone : Journal.Zone objects base cap cursor)
    (countBound : count ≤ cap) (journalAbove : cutoff ≤ base)
    (sourceEnvironment : WarmKeys.Environment source) (environment : WarmKeys.Environment ready)
    (codes : ready.code = source.code) (oracle : ready.ffi.oracle = source.ffi.oracle) (globals : HeapGlobals source ready)
    (registry : AccountDecode.Registry ready cutoff readyCursor next nextAccounts)
    (extension : AccountDecode.Registry.Extension accounts nextAccounts cursor)
    (values : TableFamily.ValuesHave ready next property) (savedValues : Journal.EntryValues entries count property)
    (frame : TableFamily.PersistentFrame cutoff cursor objects next source ready) (metadata : TableFamily.Metadata objects next)
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 count)))) :
    Result source ready cursor readyCursor cutoff protectedCursor objects next outer base cap count count entries accounts nextAccounts property property price 0 population := by
  have domain : ready.memaddrs = source.memaddrs := environment.domain.trans sourceEnvironment.domain.symm
  obtain ⟨nextImage,nextZone⟩ := Journal.image_zone_framed source ready cursor readyCursor cutoff base cap count objects next entries image zone countBound forward journalAbove frame metadata domain
  have spent : source.clock - ready.clock = paid := by rw [clock,Nat.sub_sub_self funded]
  exact {
    clockForward := by rw [clock]; exact Nat.sub_le _ _
    cursorForward := forward
    protectedBefore := before
    countForward := Nat.le_refl _
    countBound := countBound
    appends := by omega
    family := models
    image := nextImage
    zone := nextZone
    work := by rw [spent]; exact bound
    populations := populations
    code := codes
    oracle := oracle
    environment := environment
    globals := fun key notHeap _ => globals key notHeap
    values := values
    savedValues := savedValues
    registry := registry
    extension := extension
    effect := by simpa only [Nat.sub_self] using Journal.CounterEffect.unchanged source ready (globals (ofString "journal_n") (by decide))
    metadata := metadata
    frame := fun query above earlier outside _ => frame.words query above (Nat.lt_of_lt_of_le earlier before) outside
    counter := (globals (ofString "journal_n") (by decide)).trans counter
    propertyIncluded := fun _ _ owned => owned
    outerValues := fun _ => Iff.rfl
    readerKnown := fun _ _ known value owned => extension.known value (known value owned) }

end InitECandidate.Solver.Mpt.AccountMutation

#print axioms InitECandidate.Solver.Mpt.AccountMutation.heap_prefix
