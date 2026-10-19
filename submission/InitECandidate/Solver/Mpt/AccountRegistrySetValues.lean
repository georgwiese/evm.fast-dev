import InitECandidate.Solver.Mpt.AccountRegistry
import InitECandidate.Solver.MutableTable.FamilySetValues
import InitECandidate.Solver.MutableTable.FamilyPersistentFrame

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix MutableTable NaturalLayout
open Flapjack.Basis.Pure.MlString

/-- The actual original setter retains all registered account images
through real growth/relocation, alongside its whole table family, actual
cursor/count changes and amortized source price. -/
theorem Registry.set_normal_values {ι : Type} [DecidableEq ι]
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cutoff cursor : Nat)
    (objects : ι → TableFamily.Object) (writer : ι) (family : TableFamily.Model source cursor objects)
    (accounts : List (BitVec 64)) (registry : Registry source cutoff cursor objects accounts)
    (environment : GasBudget.WarmKeys.Environment source) (query value : BitVec 64) (arguments : List (ExpHOL 64))
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (owned : property writer value)
    (queryFits : query.toNat+KeyHash.keySize (objects writer).kind<2^64)
    (queryMapped : ∀ offset<KeyHash.keySize (objects writer).kind,source.memaddrs (panByteAlignHOL (width:=64) (byteAddress query offset)))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (TableCall.values (objects writer).pointer query value))
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htab_set") arguments)=(none,target)) :
    ∃ paid nextCursor next,paid≤source.clock ∧ target.clock=source.clock-paid ∧ cursor≤nextCursor ∧
      next.kind=(objects writer).kind ∧ next.floor=(objects writer).floor ∧ TableFamily.Model target nextCursor (Function.update objects writer next) ∧
      Registry target cutoff nextCursor (Function.update objects writer next) accounts ∧
      (∀ index,(Function.update objects writer next index).pointer=(objects index).pointer) ∧
      paid+GrowRuntime.growthPotential (objects writer).kind (objects writer).plan.capacity≤
        Set.noGrowthPrice (objects writer).kind (objects writer).slots.length+1+GrowRuntime.growthPotential (objects writer).kind next.plan.capacity ∧
      (objects writer).slots.length≤next.slots.length ∧ next.slots.length≤(objects writer).slots.length+1 ∧
      next.plan.capacity≤max (objects writer).plan.capacity (4*(next.slots.length+1)) ∧
      TableFamily.PersistentFrame cutoff cursor objects (Function.update objects writer next) source target ∧
      HeapGlobals source target ∧ target.code=source.code ∧ target.locals=source.locals ∧ TableFamily.ValuesHave target (Function.update objects writer next) property := by
  obtain ⟨paid,nextCursor,next,funded,clock,forward,nextKind,nextFloor,nextFamily,pointers,price,countLower,countUpper,capacity,locals,codeEq,nextEnvironment,globals,beforeWords,earlier,nextValues⟩ :=
    TableFamily.set_normal_values source target cursor objects writer family environment query value arguments property values owned queryFits queryMapped args normal
  have frame := TableFamily.PersistentFrame.of_set cutoff cursor objects writer next source target earlier
  have domain : target.memaddrs=source.memaddrs := nextEnvironment.domain.trans environment.domain.symm
  have nextRegistry := registry.framed source target cutoff cursor nextCursor objects (Function.update objects writer next) accounts frame forward domain
  exact ⟨paid,nextCursor,next,funded,clock,forward,nextKind,nextFloor,nextFamily,nextRegistry,pointers,price,countLower,countUpper,capacity,frame,globals,codeEq,locals,nextValues⟩

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.Registry.set_normal_values
