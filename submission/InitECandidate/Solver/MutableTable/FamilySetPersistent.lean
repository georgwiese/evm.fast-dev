import InitECandidate.Solver.MutableTable.FamilySet
import InitECandidate.Solver.MutableTable.FamilyPersistentFrame

namespace InitECandidate.Solver.MutableTable.TableFamily
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix.QueryBranch WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString

/-- The actual original setter derives a full persistent frame for records
outside all live pools, including after real growth and reinsertion. -/
theorem set_normal_framed {ι : Type} [DecidableEq ι] (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cutoff cursor : Nat)
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
      PersistentFrame cutoff cursor objects (Function.update objects writer next) source target ∧ target.locals = source.locals ∧ target.code = source.code ∧ GasBudget.WarmKeys.Environment target ∧ HeapGlobals source target ∧
      (∀ address : BitVec 64, address.toNat < (objects writer).floor → target.memory address = source.memory address) ∧
      ∀ address : BitVec 64, address.toNat < cursor → TableFootprint.Outside (objects writer).kind (objects writer).plan address →
        TableFootprint.Outside next.kind next.plan address ∧ target.memory address = source.memory address := by
  obtain ⟨paid,nextCursor,next,funded,clock,forward,nextKind,nextFloor,nextFamily,pointers,price,countLower,countUpper,capacity,locals,codeEq,nextEnvironment,globals,beforeWords,earlier⟩ :=
    set_normal source target cursor objects writer family environment query value arguments queryFits queryMapped args normal
  exact ⟨paid,nextCursor,next,funded,clock,forward,nextKind,nextFloor,nextFamily,pointers,price,countLower,countUpper,capacity,
    PersistentFrame.of_set cutoff cursor objects writer next source target earlier,locals,codeEq,nextEnvironment,globals,beforeWords,earlier⟩

end InitECandidate.Solver.MutableTable.TableFamily

#print axioms InitECandidate.Solver.MutableTable.TableFamily.set_normal_framed
