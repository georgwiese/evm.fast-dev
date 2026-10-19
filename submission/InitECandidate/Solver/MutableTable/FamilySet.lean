import InitECandidate.Solver.MutableTable.FamilySetValues
import InitECandidate.Solver.MutableTable.TableFamily
import InitECandidate.Solver.GasBudget.WarmKeysInvariant
import InitECandidate.Solver.MutableTable.SetEarlierFootprint

namespace InitECandidate.Solver.MutableTable.TableFamily
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix NaturalLayout

/-- An actual original setter in an arbitrary live table family. It derives
reached growth room and a common new cursor, retains every reader model and
all pairwise pool separation, and keeps every table's stable header pointer. -/
theorem set_normal {ι : Type} [DecidableEq ι] (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (objects : ι → Object) (writer : ι) (family : Model source cursor objects)
    (environment : GasBudget.WarmKeys.Environment source) (query value : BitVec 64) (arguments : List (ExpHOL 64))
    (queryFits : query.toNat + KeyHash.keySize (objects writer).kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize (objects writer).kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (TableCall.values (objects writer).pointer query value))
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "htab_set") arguments) = (none, target)) :
    ∃ (paid nextCursor : Nat) (next : Object),
      paid ≤ source.clock ∧ target.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧
      next.kind = (objects writer).kind ∧ next.floor = (objects writer).floor ∧
      Model target nextCursor (Function.update objects writer next) ∧
      (∀ index, (Function.update objects writer next index).pointer = (objects index).pointer) ∧
      paid + GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity ≤
        Set.noGrowthPrice (objects writer).kind (objects writer).slots.length + 1 + GrowRuntime.growthPotential (objects writer).kind next.plan.capacity ∧
      (objects writer).slots.length ≤ next.slots.length ∧ next.slots.length ≤ (objects writer).slots.length + 1 ∧
      next.plan.capacity ≤ max (objects writer).plan.capacity (4 * (next.slots.length + 1)) ∧
      target.locals = source.locals ∧ target.code = source.code ∧ GasBudget.WarmKeys.Environment target ∧ HeapGlobals source target ∧
      (∀ address : BitVec 64, address.toNat < (objects writer).floor → target.memory address = source.memory address) ∧
      ∀ address : BitVec 64, address.toNat < cursor → TableFootprint.Outside (objects writer).kind (objects writer).plan address →
        TableFootprint.Outside next.kind next.plan address ∧ target.memory address = source.memory address := by
  obtain ⟨paid, nextCursor, next, funded, clock, forward, nextKind, nextFloor, nextFamily, pointers, price,
    countLower, countUpper, capacity, locals, codeEq, nextEnvironment, globals, beforeWords, earlier, _⟩ :=
    set_normal_values source target cursor objects writer family environment query value arguments
      (fun _ _=>True) (fun _ _ _ _ _ _=>True.intro) True.intro queryFits queryMapped args normal
  exact ⟨paid, nextCursor, next, funded, clock, forward, nextKind, nextFloor, nextFamily, pointers, price,
    countLower, countUpper, capacity, locals, codeEq, nextEnvironment, globals, beforeWords, earlier⟩

end InitECandidate.Solver.MutableTable.TableFamily

#print axioms InitECandidate.Solver.MutableTable.TableFamily.set_normal
