import InitECandidate.Solver.GasBudget.AccountCachePrefix

namespace InitECandidate.Solver.GasBudget.AccountOptional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout

set_option maxHeartbeats 2000000 in
/-- The actual original account lookup records its read and reaches the
transaction-cache result with the full family retained through real growth. -/
theorem normal_cache_prefix {ι : Type} [DecidableEq ι] (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (transaction query : BitVec 64) (cursor : Nat) (objects : ι → TableFamily.Object) (writer reader : ι)
    (family : TableFamily.Model source cursor objects)
    (writerKind : (objects writer).kind = .account) (readerKind : (objects reader).kind = .account)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (transactionGlobal : source.globals.lookup (ofString "ts") = some (.val (.word transaction)))
    (recordBefore : transaction.toNat + 72 ≤ (objects writer).floor)
    (setMapped : source.memaddrs (transaction + 8#64)) (setCell : source.memory (transaction + 8#64) = .word (objects writer).pointer)
    (getMapped : source.memaddrs (transaction + 16#64)) (getCell : source.memory (transaction + 16#64) = .word (objects reader).pointer)
    (queryLocal : source.locals.lookup (ofString "addr") = some (.val (.word query)))
    (queryFits : query.toNat + 20 < 2^64)
    (queryMapped : ∀ offset < 20, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress query offset)))
    (returned : ValueHOL 64) (run : evaluateHOLFiniteState source body = (some (.returned returned), post)) :
    ∃ (paid nextCursor : Nat) (next : TableFamily.Object) (flag value : BitVec 64)
      (ready inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      paid ≤ source.clock ∧ ready.clock = source.clock - paid ∧
      paid + GrowRuntime.growthPotential .account (objects writer).plan.capacity ≤
        9 * (objects writer).slots.length + 8 * (Function.update objects writer next reader).slots.length + 15 +
          GrowRuntime.growthPotential .account next.plan.capacity ∧
      next.kind = .account ∧ TableFamily.Model ready nextCursor (Function.update objects writer next) ∧
      (∀ index, (Function.update objects writer next index).pointer = (objects index).pointer) ∧
      WarmKeys.Environment ready ∧ HeapGlobals source ready ∧
      TableFamily.FloorFrame objects (Function.update objects writer next) source ready ∧
      (flag = 0#64 ∨ flag = 1#64) ∧
      ready.locals.lookup (ofString "addr") = some (.val (.word query)) ∧
      ready.locals.lookup (ofString "w") = some (Get.pair flag value) ∧
      evaluateHOLFiniteState ready afterGet = (some (.returned returned), inner) ∧
      Input.LocalEffects.erase post = Input.LocalEffects.erase inner ∧ post.clock = inner.clock := by
  exact AccountCache.normal_cache_prefix .transaction source post transaction transaction query cursor objects writer reader family
    writerKind readerKind environment installed transactionGlobal transactionGlobal recordBefore setMapped setCell getMapped getCell
    queryLocal queryFits queryMapped returned run

end InitECandidate.Solver.GasBudget.AccountOptional

#print axioms InitECandidate.Solver.GasBudget.AccountOptional.normal_cache_prefix
