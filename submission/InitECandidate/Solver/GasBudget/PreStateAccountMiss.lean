import InitECandidate.Solver.GasBudget.AccountCacheCases
import InitECandidate.Solver.GasBudget.PreStateReadRecordCall
import InitECandidate.Solver.GasBudget.PreStateReadRecordSafe
import InitECandidate.Solver.Input.EvaluationOracle

namespace InitECandidate.Solver.GasBudget.AccountCache
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout

def witnessAccountCall : ProgHOL 64 := .decCall (ofString "a") .one (ofString "ws_get_account_optional")
  [localVar "addr"] (.return (localVar "a"))

/-- A real block-cache miss records its pre-state read before entering the
actual witness-account provider, deriving the next family and same query. -/
theorem pre_state_miss_for_outcome_values (outcome : Outcome) {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (block query : BitVec 64)
    (cursor : Nat) (objects : ι → TableFamily.Object) (writer : ι)
    (family : TableFamily.Model source cursor objects) (kind : (objects writer).kind = .account)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (property : ι → BitVec 64 → Prop) (tableValues : TableFamily.ValuesHave source objects property) (owned : property writer 1#64)
    (blockGlobal : source.globals.lookup (ofString "bs") = some (.val (.word block)))
    (mapped : source.memaddrs (block + 72#64)) (stored : source.memory (block + 72#64) = .word (objects writer).pointer)
    (queryLocal : source.locals.lookup (ofString "addr") = some (.val (.word query)))
    (queryFits : query.toNat + 20 < 2^64)
    (queryMapped : ∀ offset < 20, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress query offset)))
    (run : evaluateHOLFiniteState source Kind.preState.afterMiss = (outcome.result, post)) :
    ∃ (paid nextCursor : Nat) (next : TableFamily.Object) (ready : PanSemStateFiniteExact 64 Guest.HostMemory),
      paid ≤ source.clock ∧ ready.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧ next.kind = .account ∧
      paid + GrowRuntime.growthPotential .account (objects writer).plan.capacity ≤
        9 * (objects writer).slots.length + 13 + GrowRuntime.growthPotential .account next.plan.capacity ∧
      TableFamily.Model ready nextCursor (Function.update objects writer next) ∧
      (∀ index, (Function.update objects writer next index).pointer = (objects index).pointer) ∧
      (objects writer).slots.length ≤ next.slots.length ∧ next.slots.length ≤ (objects writer).slots.length + 1 ∧
      next.plan.capacity ≤ max (objects writer).plan.capacity (4 * (next.slots.length + 1)) ∧
      ready.code = source.code ∧ ready.ffi.oracle=source.ffi.oracle ∧ WarmKeys.Environment ready ∧ HeapGlobals source ready ∧
      TableFamily.FloorFrame objects (Function.update objects writer next) source ready ∧
      ready.locals.lookup (ofString "addr") = some (.val (.word query)) ∧
      evaluateHOLFiniteState ready witnessAccountCall = (outcome.result, post) ∧
      TableFamily.ValuesHave ready (Function.update objects writer next) property ∧
      TableFamily.PersistentFrame 0 cursor objects (Function.update objects writer next) source ready := by
  rw [pre_state_miss_shape] at run
  have safe : Input.LocalPrefix (ofString "addr")
      (.call (some (none, none)) (ofString "record_pre_state_read") [localVar "addr"]) :=
    .call none _ _ (by intro name impossible; cases impossible)
  have exposed : ∃ ready,
      evaluateHOLFiniteState source (.call (some (none, none)) (ofString "record_pre_state_read") [localVar "addr"]) = (none, ready) ∧
      evaluateHOLFiniteState ready witnessAccountCall = (outcome.result, post) := by
    cases outcome with
    | returned value =>
      obtain ⟨ready, recordRun, tailRun, saved⟩ := safe.normal_continue source post witnessAccountCall value run
      exact ⟨ready, recordRun, tailRun⟩
    | exception identifier payload other =>
      rcases Input.sequence_exception source post
          (.call (some (none, none)) (ofString "record_pre_state_read") [localVar "addr"]) witnessAccountCall identifier payload run with failed | continued
      · have excluded := Input.NoNamedException.call_body source.code identifier (ofString "record_pre_state_read") [localVar "addr"]
          PreStateReadRecord.formals PreStateReadRecord.body .one (PreStateReadRecord.original_code source.code installed)
          (PreStateReadRecord.no_other_exception source environment identifier other)
        exact (excluded source rfl payload (congrArg Prod.fst failed)).elim
      · exact continued
  obtain ⟨ready, recordRun, tailRun⟩ := exposed
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [localVar "addr"] = some [.val (.word query)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, queryLocal]
  obtain ⟨paid, nextCursor, next, funded, clock, forward, nextKind, nextFamily, pointers, amortized,
    countLower, countUpper, capacity, codes, nextEnvironment, globals, floorFrame, locals, nextValues, persistent⟩ :=
    PreStateReadRecord.call_normal_values source ready block query cursor objects writer family kind environment installed property tableValues owned blockGlobal mapped stored
      queryFits queryMapped [localVar "addr"] args recordRun
  refine ⟨paid, nextCursor, next, ready, funded, clock, forward, nextKind, amortized, nextFamily, pointers,
    countLower, countUpper, capacity, codes, Input.evaluation_oracle source ready _ none recordRun, nextEnvironment, globals, floorFrame, ?_, tailRun, nextValues, persistent⟩
  rw [locals]
  exact queryLocal

theorem pre_state_miss_for_outcome (outcome : Outcome) {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (block query : BitVec 64)
    (cursor : Nat) (objects : ι → TableFamily.Object) (writer : ι)
    (family : TableFamily.Model source cursor objects) (kind : (objects writer).kind = .account)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (blockGlobal : source.globals.lookup (ofString "bs") = some (.val (.word block)))
    (mapped : source.memaddrs (block + 72#64)) (stored : source.memory (block + 72#64) = .word (objects writer).pointer)
    (queryLocal : source.locals.lookup (ofString "addr") = some (.val (.word query)))
    (queryFits : query.toNat + 20 < 2^64)
    (queryMapped : ∀ offset < 20, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress query offset)))
    (run : evaluateHOLFiniteState source Kind.preState.afterMiss = (outcome.result, post)) :
    ∃ (paid nextCursor : Nat) (next : TableFamily.Object) (ready : PanSemStateFiniteExact 64 Guest.HostMemory),
      paid ≤ source.clock ∧ ready.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧ next.kind = .account ∧
      paid + GrowRuntime.growthPotential .account (objects writer).plan.capacity ≤
        9 * (objects writer).slots.length + 13 + GrowRuntime.growthPotential .account next.plan.capacity ∧
      TableFamily.Model ready nextCursor (Function.update objects writer next) ∧
      (∀ index, (Function.update objects writer next index).pointer = (objects index).pointer) ∧
      (objects writer).slots.length ≤ next.slots.length ∧ next.slots.length ≤ (objects writer).slots.length + 1 ∧
      next.plan.capacity ≤ max (objects writer).plan.capacity (4 * (next.slots.length + 1)) ∧
      ready.code = source.code ∧ ready.ffi.oracle=source.ffi.oracle ∧ WarmKeys.Environment ready ∧ HeapGlobals source ready ∧
      TableFamily.FloorFrame objects (Function.update objects writer next) source ready ∧
      ready.locals.lookup (ofString "addr") = some (.val (.word query)) ∧
      evaluateHOLFiniteState ready witnessAccountCall = (outcome.result, post) := by
  obtain ⟨paid,nextCursor,next,ready,funded,clock,forward,nextKind,price,nextFamily,pointers,countLower,countUpper,capacity,codes,oracleEq,nextEnvironment,globals,floorFrame,queryCell,tailRun,_,_⟩ :=
    pre_state_miss_for_outcome_values outcome source post block query cursor objects writer family kind environment installed
      (fun _ _=>True) (fun _ _ _ _ _ _=>True.intro) True.intro blockGlobal mapped stored queryLocal queryFits queryMapped run
  exact ⟨paid,nextCursor,next,ready,funded,clock,forward,nextKind,price,nextFamily,pointers,countLower,countUpper,capacity,codes,oracleEq,nextEnvironment,globals,floorFrame,queryCell,tailRun⟩

theorem pre_state_miss_normal_values {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (block query : BitVec 64)
    (cursor : Nat) (objects : ι → TableFamily.Object) (writer : ι)
    (family : TableFamily.Model source cursor objects) (kind : (objects writer).kind = .account)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (property : ι → BitVec 64 → Prop) (tableValues : TableFamily.ValuesHave source objects property) (owned : property writer 1#64)
    (blockGlobal : source.globals.lookup (ofString "bs") = some (.val (.word block)))
    (mapped : source.memaddrs (block + 72#64)) (stored : source.memory (block + 72#64) = .word (objects writer).pointer)
    (queryLocal : source.locals.lookup (ofString "addr") = some (.val (.word query)))
    (queryFits : query.toNat + 20 < 2^64)
    (queryMapped : ∀ offset < 20, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress query offset)))
    (returned : ValueHOL 64) (run : evaluateHOLFiniteState source Kind.preState.afterMiss = (some (.returned returned), post)) :
    ∃ (paid nextCursor : Nat) (next : TableFamily.Object) (ready : PanSemStateFiniteExact 64 Guest.HostMemory),
      paid ≤ source.clock ∧ ready.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧ next.kind = .account ∧
      paid + GrowRuntime.growthPotential .account (objects writer).plan.capacity ≤
        9 * (objects writer).slots.length + 13 + GrowRuntime.growthPotential .account next.plan.capacity ∧
      TableFamily.Model ready nextCursor (Function.update objects writer next) ∧
      (∀ index, (Function.update objects writer next index).pointer = (objects index).pointer) ∧
      (objects writer).slots.length ≤ next.slots.length ∧ next.slots.length ≤ (objects writer).slots.length + 1 ∧
      next.plan.capacity ≤ max (objects writer).plan.capacity (4 * (next.slots.length + 1)) ∧
      ready.code = source.code ∧ ready.ffi.oracle=source.ffi.oracle ∧ WarmKeys.Environment ready ∧ HeapGlobals source ready ∧
      TableFamily.FloorFrame objects (Function.update objects writer next) source ready ∧
      ready.locals.lookup (ofString "addr") = some (.val (.word query)) ∧
      evaluateHOLFiniteState ready witnessAccountCall = (some (.returned returned), post) ∧
      TableFamily.ValuesHave ready (Function.update objects writer next) property ∧
      TableFamily.PersistentFrame 0 cursor objects (Function.update objects writer next) source ready := by
  exact pre_state_miss_for_outcome_values (.returned returned) source post block query cursor objects writer family kind environment installed property tableValues owned blockGlobal mapped stored
    queryLocal queryFits queryMapped run

theorem pre_state_miss_normal {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (block query : BitVec 64)
    (cursor : Nat) (objects : ι → TableFamily.Object) (writer : ι)
    (family : TableFamily.Model source cursor objects) (kind : (objects writer).kind = .account)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (blockGlobal : source.globals.lookup (ofString "bs") = some (.val (.word block)))
    (mapped : source.memaddrs (block + 72#64)) (stored : source.memory (block + 72#64) = .word (objects writer).pointer)
    (queryLocal : source.locals.lookup (ofString "addr") = some (.val (.word query)))
    (queryFits : query.toNat + 20 < 2^64)
    (queryMapped : ∀ offset < 20, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress query offset)))
    (returned : ValueHOL 64) (run : evaluateHOLFiniteState source Kind.preState.afterMiss = (some (.returned returned), post)) :
    ∃ (paid nextCursor : Nat) (next : TableFamily.Object) (ready : PanSemStateFiniteExact 64 Guest.HostMemory),
      paid ≤ source.clock ∧ ready.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧ next.kind = .account ∧
      paid + GrowRuntime.growthPotential .account (objects writer).plan.capacity ≤
        9 * (objects writer).slots.length + 13 + GrowRuntime.growthPotential .account next.plan.capacity ∧
      TableFamily.Model ready nextCursor (Function.update objects writer next) ∧
      (∀ index, (Function.update objects writer next index).pointer = (objects index).pointer) ∧
      (objects writer).slots.length ≤ next.slots.length ∧ next.slots.length ≤ (objects writer).slots.length + 1 ∧
      next.plan.capacity ≤ max (objects writer).plan.capacity (4 * (next.slots.length + 1)) ∧
      ready.code = source.code ∧ ready.ffi.oracle=source.ffi.oracle ∧ WarmKeys.Environment ready ∧ HeapGlobals source ready ∧
      TableFamily.FloorFrame objects (Function.update objects writer next) source ready ∧
      ready.locals.lookup (ofString "addr") = some (.val (.word query)) ∧
      evaluateHOLFiniteState ready witnessAccountCall = (some (.returned returned), post) := by
  exact pre_state_miss_for_outcome (.returned returned) source post block query cursor objects writer family kind environment installed blockGlobal mapped stored
    queryLocal queryFits queryMapped run

theorem pre_state_miss_exception {ι : Type} [DecidableEq ι]
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (block query : BitVec 64)
    (cursor : Nat) (objects : ι → TableFamily.Object) (writer : ι)
    (family : TableFamily.Model source cursor objects) (kind : (objects writer).kind = .account)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (blockGlobal : source.globals.lookup (ofString "bs") = some (.val (.word block)))
    (mapped : source.memaddrs (block + 72#64)) (stored : source.memory (block + 72#64) = .word (objects writer).pointer)
    (queryLocal : source.locals.lookup (ofString "addr") = some (.val (.word query)))
    (queryFits : query.toNat + 20 < 2^64)
    (queryMapped : ∀ offset < 20, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress query offset)))
    (identifier : MlS) (payload : ValueHOL 64) (other : ofString "TrapErr" ≠ identifier)
    (run : evaluateHOLFiniteState source Kind.preState.afterMiss = (some (.exception identifier payload), post)) :
    ∃ (paid nextCursor : Nat) (next : TableFamily.Object) (ready : PanSemStateFiniteExact 64 Guest.HostMemory),
      paid ≤ source.clock ∧ ready.clock = source.clock - paid ∧ cursor ≤ nextCursor ∧ next.kind = .account ∧
      paid + GrowRuntime.growthPotential .account (objects writer).plan.capacity ≤
        9 * (objects writer).slots.length + 13 + GrowRuntime.growthPotential .account next.plan.capacity ∧
      TableFamily.Model ready nextCursor (Function.update objects writer next) ∧
      (∀ index, (Function.update objects writer next index).pointer = (objects index).pointer) ∧
      (objects writer).slots.length ≤ next.slots.length ∧ next.slots.length ≤ (objects writer).slots.length + 1 ∧
      next.plan.capacity ≤ max (objects writer).plan.capacity (4 * (next.slots.length + 1)) ∧
      ready.code = source.code ∧ ready.ffi.oracle=source.ffi.oracle ∧ WarmKeys.Environment ready ∧ HeapGlobals source ready ∧
      TableFamily.FloorFrame objects (Function.update objects writer next) source ready ∧
      ready.locals.lookup (ofString "addr") = some (.val (.word query)) ∧
      evaluateHOLFiniteState ready witnessAccountCall = (some (.exception identifier payload), post) := by
  exact pre_state_miss_for_outcome (.exception identifier payload other) source post block query cursor objects writer family kind environment installed blockGlobal mapped stored
    queryLocal queryFits queryMapped run

end InitECandidate.Solver.GasBudget.AccountCache

#print axioms InitECandidate.Solver.GasBudget.AccountCache.pre_state_miss_for_outcome_values
#print axioms InitECandidate.Solver.GasBudget.AccountCache.pre_state_miss_normal_values
#print axioms InitECandidate.Solver.GasBudget.AccountCache.pre_state_miss_for_outcome
#print axioms InitECandidate.Solver.GasBudget.AccountCache.pre_state_miss_normal
#print axioms InitECandidate.Solver.GasBudget.AccountCache.pre_state_miss_exception
