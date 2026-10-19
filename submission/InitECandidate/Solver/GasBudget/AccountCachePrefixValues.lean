import InitECandidate.Solver.MutableTable.FamilySetValues
import InitECandidate.Solver.MutableTable.FamilyPersistentFrame
import InitECandidate.Solver.GasBudget.AccountCacheOutcome
import InitECandidate.Solver.Input.EvaluationOracle

namespace InitECandidate.Solver.GasBudget.AccountCache
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout

set_option maxHeartbeats 2000000 in
/-- The actual original account lookup records its read and reaches the
transaction-cache result with the full family retained through real growth. -/
theorem outcome_cache_prefix_values (outcome : Outcome) (kind : Kind) {ι : Type} [DecidableEq ι] (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (transaction readerRecord query : BitVec 64) (cursor : Nat) (objects : ι → TableFamily.Object) (writer reader : ι)
    (family : TableFamily.Model source cursor objects)
    (writerKind : (objects writer).kind = .account) (readerKind : (objects reader).kind = .account)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (property : ι → BitVec 64 → Prop) (values : TableFamily.ValuesHave source objects property) (owned : property writer 1#64)
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
      TableFamily.PersistentFrame 0 cursor objects (Function.update objects writer next) source ready := by
  classical
  have setRead := Input.global_field_read source "ts" transaction 8#64 (objects writer).pointer transactionGlobal setMapped setCell
  have setArgs : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) setArguments =
      some (TableCall.values (objects writer).pointer query 1#64) := by
    simp only [eval] at setRead
    change evalListHOLExact source.toExact setArguments = _
    simp only [setArguments, AccountOptional.setArguments, evalListHOLExact]
    simp only [AccountOptional.tableField]
    rw [setRead]
    simp [TableCall.values, evalListHOLExact, evalHOLExact, toExact, localVar, queryLocal]
  obtain ⟨called, setRun, getterRun⟩ := set_before_outcome outcome kind source post environment run
  obtain ⟨setPaid, nextCursor, next, setFits, setClock, forward, nextKind, nextFloor, nextFamily, pointers, amortized,
    countLower, countUpper, capacity, locals, codes, nextEnvironment, globals, protectedWords, earlier, nextValues⟩ :=
    TableFamily.set_normal_values source called cursor objects writer family environment query 1#64 setArguments property values owned
      (by rw [writerKind]; exact queryFits) (by rw [writerKind]; exact queryMapped) setArgs setRun
  rw [writerKind, Set.no_growth_caller_price] at amortized
  change setPaid + GrowRuntime.growthPotential .account (objects writer).plan.capacity ≤
    9 * (objects writer).slots.length + 12 + GrowRuntime.growthPotential .account next.plan.capacity at amortized
  let cache := Function.update objects writer next reader
  have cacheKind : cache.kind = .account := by
    by_cases same : reader = writer
    · subst reader
      simpa only [cache, Function.update_self] using nextKind.trans writerKind
    · simpa only [cache, Function.update_of_ne same] using readerKind
  have cacheTable : TableState called .account cache.plan cache.slots nextCursor cache.floor := by
    have current := nextFamily.tables reader
    change TableState called cache.kind cache.plan cache.slots nextCursor cache.floor at current
    rw [cacheKind] at current
    exact current
  have currentOriginal : Input.OriginalCode.Installed called.code := by rw [codes]; exact installed
  have currentReader : called.globals.lookup (ofString kind.readerGlobal) = some (.val (.word readerRecord)) :=
    (globals (ofString kind.readerGlobal) (by cases kind <;> decide)).trans readerGlobal
  have currentMapped : called.memaddrs (readerRecord + 16#64) := by rw [nextEnvironment.domain, ← environment.domain]; exact getMapped
  have floorSmall : (objects writer).floor < 2^64 := by
    have lower := (family.tables writer).lower .header
    have upper := (family.tables writer).valid.upper .header
    change (objects writer).plan.base .header + 72 ≤ 33806089496 at upper
    omega
  have readerNumber : (readerRecord + 16#64).toNat = readerRecord.toNat + 16 :=
    BitVec.toNat_add_of_lt (by change readerRecord.toNat + 16 < 2^64; omega)
  have currentStored : called.memory (readerRecord + 16#64) = .word cache.pointer := by
    rw [protectedWords _ (by rw [readerNumber]; omega), getCell]
    have stable := pointers reader
    change cache.pointer = (objects reader).pointer at stable
    rw [stable]
  have getterRead := Input.global_field_read called kind.readerGlobal readerRecord 16#64 cache.pointer currentReader currentMapped currentStored
  have currentQuery : called.locals.lookup (ofString "addr") = some (.val (.word query)) := by rw [locals]; exact queryLocal
  have getArgs : evalListHOLFinite called (h := fun address => Classical.propDecidable (called.memaddrs address)) kind.getArguments =
      some [.val (.word (cell cache.plan .header 0)), .val (.word query)] := by
    simp only [eval] at getterRead
    change evalListHOLExact called.toExact kind.getArguments = _
    rw [Kind.getArguments, evalListHOLExact]
    rw [getterRead]
    simp [TableFamily.Object.pointer, evalListHOLExact, evalHOLExact, toExact, localVar, currentQuery]
  have currentQueryMapped : ∀ offset < 20, called.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress query offset)) := by
    intro offset inside
    rw [nextEnvironment.domain, ← environment.domain]
    exact queryMapped offset inside
  rw [kind.getter_shape] at getterRun
  obtain ⟨getPaid, flag, value, inner, getPositive, getBound, getFits, binary, origin, tailRun, scope⟩ :=
    getter_before_outcome_origin outcome called post .account cache.plan cache.slots nextCursor cache.floor cacheTable nextEnvironment query queryFits currentQueryMapped
      (Get.original_code called.code currentOriginal) "w" kind.getArguments kind.afterGet getArgs getterRun
  let ready := setVarHOLFinite (ofString "w") (Get.pair flag value) {called with clock := called.clock - getPaid}
  have returnedOwnership := origin.occupied_property called (cell cache.plan .values 0) (BitVec.ofNat 64 cache.plan.capacity)
    flag value cache.slots (property reader) (nextValues reader)
  have persistent := TableFamily.PersistentFrame.of_set 0 cursor objects writer next source ready earlier
  have funded : setPaid + getPaid ≤ source.clock := by rw [setClock] at getFits; omega
  have clock : ready.clock = source.clock - (setPaid + getPaid) := by change called.clock - getPaid = _; rw [setClock]; omega
  change getPaid ≤ 8 * (Function.update objects writer next reader).slots.length + 3 at getBound
  refine ⟨setPaid + getPaid, nextCursor, next, flag, value, ready, inner, funded, clock, by omega,
    nextKind.trans writerKind, forward, countLower, countUpper, capacity, nextFamily.of_control rfl rfl rfl rfl, pointers, codes,
    Input.evaluation_oracle source called setCall none setRun, nextEnvironment.of_fields rfl rfl rfl,
    globals, TableFamily.FloorFrame.of_update objects writer next source ready nextFloor protectedWords, protectedWords, binary, ?_, ?_, tailRun, ?_, ?_, nextValues, returnedOwnership, persistent⟩
  · simpa [ready, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString] using currentQuery
  · simp [ready, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · rw [scope]; rfl
  · rw [scope]; rfl

end InitECandidate.Solver.GasBudget.AccountCache

#print axioms InitECandidate.Solver.GasBudget.AccountCache.outcome_cache_prefix_values
