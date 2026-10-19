import InitECandidate.Solver.GasBudget.AccountCachePrefixValues
import InitECandidate.Solver.Mpt.AccountRegistry

namespace InitECandidate.Solver.GasBudget.AccountCache
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout

/-- Current occupied cache ownership and real mutation frames establish a
physical account image on every actual present non-sentinel cache result. -/
theorem outcome_cache_prefix_registered (outcome : Outcome) (kind : Kind) {ι : Type} [DecidableEq ι] (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (transaction readerRecord query : BitVec 64) (cursor : Nat) (objects : ι → TableFamily.Object) (writer reader : ι)
    (family : TableFamily.Model source cursor objects)
    (writerKind : (objects writer).kind = .account) (readerKind : (objects reader).kind = .account)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (owned : property writer 1#64)
    (cutoff : Nat) (accounts : List (BitVec 64))
    (registry : Mpt.AccountDecode.Registry source cutoff cursor objects accounts)
    (cacheKnown : ∀ value,property reader value → Mpt.AccountDecode.Registry.Known accounts value)
    (transactionGlobal : source.globals.lookup (ofString "ts") = some (.val (.word transaction)))
    (readerGlobal : source.globals.lookup (ofString kind.readerGlobal) = some (.val (.word readerRecord)))
    (recordBefore : readerRecord.toNat + 72 ≤ (objects writer).floor)
    (setMapped : source.memaddrs (transaction + 8#64)) (setCell : source.memory (transaction + 8#64) = .word (objects writer).pointer)
    (getMapped : source.memaddrs (readerRecord + 16#64)) (getCell : source.memory (readerRecord + 16#64) = .word (objects reader).pointer)
    (queryLocal : source.locals.lookup (ofString "addr") = some (.val (.word query)))
    (queryFits : query.toNat + 20 < 2^64)
    (queryMapped : ∀ offset < 20, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress query offset)))
    (run : evaluateHOLFiniteState source kind.body = (outcome.result, post)) :
    ∃ (paid nextCursor : Nat) (next : TableFamily.Object) (flag value : BitVec 64)
      (ready inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      paid ≤ source.clock ∧ ready.clock = source.clock - paid ∧
      paid + GrowRuntime.growthPotential .account (objects writer).plan.capacity ≤
        9 * (objects writer).slots.length + 8 * (Function.update objects writer next reader).slots.length + 15 +
          GrowRuntime.growthPotential .account next.plan.capacity ∧
      next.kind = .account ∧ cursor≤nextCursor ∧ (objects writer).slots.length≤next.slots.length ∧ next.slots.length≤(objects writer).slots.length+1 ∧
      next.plan.capacity≤max (objects writer).plan.capacity (4*(next.slots.length+1)) ∧ TableFamily.Model ready nextCursor (Function.update objects writer next) ∧
      (∀ index, (Function.update objects writer next index).pointer = (objects index).pointer) ∧
      ready.code=source.code ∧ ready.ffi.oracle=source.ffi.oracle ∧ WarmKeys.Environment ready ∧ HeapGlobals source ready ∧
      TableFamily.FloorFrame objects (Function.update objects writer next) source ready ∧
      (∀ address : BitVec 64,address.toNat<(objects writer).floor → ready.memory address=source.memory address) ∧
      (flag = 0#64 ∨ flag = 1#64) ∧
      ready.locals.lookup (ofString "addr") = some (.val (.word query)) ∧
      ready.locals.lookup (ofString "w") = some (Get.pair flag value) ∧
      evaluateHOLFiniteState ready kind.afterGet = (outcome.result, inner) ∧
      Input.LocalEffects.erase post = Input.LocalEffects.erase inner ∧ post.clock = inner.clock ∧
      TableFamily.ValuesHave ready (Function.update objects writer next) property ∧ (flag=0#64 ∨ property reader value) ∧
      TableFamily.PersistentFrame 0 cursor objects (Function.update objects writer next) source ready ∧
      Mpt.AccountDecode.Registry ready cutoff nextCursor (Function.update objects writer next) accounts ∧
      (flag=0#64 ∨ value=1#64 ∨ Nonempty (Mpt.AccountDecode.Image ready value)) := by
  obtain ⟨paid,nextCursor,next,flag,value,ready,inner,funded,clock,price,nextKind,forward,countLower,countUpper,capacity,nextFamily,pointers,
    codeEq,oracleEq,nextEnvironment,globals,floorFrame,beforeWords,binary,addressLocal,pairLocal,tailRun,erased,endClock,nextValues,ownership,persistent⟩ :=
    outcome_cache_prefix_values outcome kind source post transaction readerRecord query cursor objects writer reader family writerKind readerKind environment installed
      property values owned transactionGlobal readerGlobal recordBefore setMapped setCell getMapped getCell queryLocal queryFits queryMapped run
  have scopedFrame : TableFamily.PersistentFrame cutoff cursor objects (Function.update objects writer next) source ready :=
    ⟨fun address lower earlier outside=>persistent.words address (Nat.zero_le _) earlier outside⟩
  have nextRegistry := registry.framed source ready cutoff cursor nextCursor objects (Function.update objects writer next) accounts scopedFrame forward
    (nextEnvironment.domain.trans environment.domain.symm)
  have image : flag=0#64 ∨ value=1#64 ∨ Nonempty (Mpt.AccountDecode.Image ready value) := by
    rcases ownership with absent | occupied
    · exact Or.inl absent
    · right
      rcases cacheKnown value occupied with absent | member
      · exact Or.inl absent
      · exact Or.inr (nextRegistry.images value member)
  exact ⟨paid,nextCursor,next,flag,value,ready,inner,funded,clock,price,nextKind,forward,countLower,countUpper,capacity,nextFamily,pointers,
    codeEq,oracleEq,nextEnvironment,globals,floorFrame,beforeWords,binary,addressLocal,pairLocal,tailRun,erased,endClock,nextValues,ownership,persistent,nextRegistry,image⟩

end InitECandidate.Solver.GasBudget.AccountCache

#print axioms InitECandidate.Solver.GasBudget.AccountCache.outcome_cache_prefix_registered
