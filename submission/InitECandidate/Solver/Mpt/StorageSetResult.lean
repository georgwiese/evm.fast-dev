import InitECandidate.Solver.Mpt.StorageSetPresent
import InitECandidate.Solver.Mpt.StorageSetAbsent
import InitECandidate.Solver.MutableTable.FamilyNewPotential

namespace InitECandidate.Solver.Mpt.StorageSet
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable NaturalLayout GasBudget
open Flapjack.Basis.Pure.MlString

def tailPrice (population : Nat) (created : Bool) : Nat :=
  if created then TableRuntime.price 8 + Journal.Append.setPrice .account population + Journal.Append.setPrice .word 0 + 4
  else Journal.Append.setPrice .word population + 2

theorem set_price_mono (kind : KeyHash.Kind) (first second : Nat) (ordered : first ≤ second) :
    Journal.Append.setPrice kind first ≤ Journal.Append.setPrice kind second := by
  cases kind <;> simp [Journal.Append.setPrice,Get.bodyPrice,Set.noGrowthPrice,Insert.findPrice,Insert.rawPrice,
    Find.generalProbePrice,KeyHash.keySize,KeyHash.hashPrice,MemeqByteRuntime.price] <;> omega

theorem word_set_price (population : Nat) : Journal.Append.setPrice .word population = 13 * population + 47 := by
  simp [Journal.Append.setPrice,Get.bodyPrice,Set.noGrowthPrice,Insert.findPrice,Insert.rawPrice,
    Find.generalProbePrice,KeyHash.keySize,KeyHash.hashPrice,MemeqByteRuntime.price]
  omega

/-- The index family may gain one actual inner table. The embedding retains
every old header identity; current occupied/undo predicates and outer references
are transported together with the physical states and whole-family potential. -/
def Result {ι : Type} [Fintype ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor cutoff population : Nat)
    (objects : ι → TableFamily.Object) (outer : ι) (base cap count : Nat)
    (accounts : List (BitVec 64)) (property : ι → BitVec 64 → Prop) (budget : Bool → Nat) : Prop :=
  ∃ (κ : Type) (finite : Fintype κ) (embed : ι → κ) (next : κ → TableFamily.Object) (nextProperty : κ → BitVec 64 → Prop)
    (paid nextCursor added : Nat) (created : Bool) (nextEntries : Nat → Journal.Entry κ),
    Function.Injective embed ∧ @Fintype.card κ finite ≤ Fintype.card ι + 1 ∧
    paid ≤ source.clock ∧ post.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧ added = (if created then 2 else 1) ∧ count + added ≤ cap ∧
    TableFamily.Model post nextCursor next ∧ Journal.Image post next base (count + added) nextEntries ∧ Journal.Zone next base cap nextCursor ∧
    paid + TableFamily.potential objects ≤ budget created + @TableFamily.potential κ finite next ∧
    (∀ reader,(next reader).slots.length ≤ population + 1) ∧
    post.code = source.code ∧ WarmKeys.Environment post ∧ Journal.OtherGlobals source post ∧
    TableFamily.ValuesHave post next nextProperty ∧ Journal.EntryValues nextEntries (count + added) nextProperty ∧
    AccountDecode.Registry post cutoff nextCursor next accounts ∧ Journal.CounterEffect source post added 0 0 ∧
    (∀ query : BitVec 64,query.toNat < cursor → TableFamily.Outside objects query → Journal.Away base cap query → TableFamily.Outside next query ∧ post.memory query = source.memory query) ∧
    (∀ reader,(next (embed reader)).kind = (objects reader).kind ∧ (next (embed reader)).floor = (objects reader).floor ∧ (next (embed reader)).pointer = (objects reader).pointer) ∧
    post.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 (count + added)))) ∧
    (∀ reader value,property reader value → nextProperty (embed reader) value) ∧
    (∀ reader,reader ≠ outer → ∀ value,nextProperty (embed reader) value ↔ property reader value) ∧
    (∀ value,nextProperty (embed outer) value → ∃ reader,(next reader).pointer = value ∧ (next reader).kind = .word)

end InitECandidate.Solver.Mpt.StorageSet

#print axioms InitECandidate.Solver.Mpt.StorageSet.set_price_mono
#print axioms InitECandidate.Solver.Mpt.StorageSet.word_set_price
