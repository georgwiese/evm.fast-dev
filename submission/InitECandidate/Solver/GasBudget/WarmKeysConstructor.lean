import InitECandidate.Solver.GasBudget.WarmKeysConstructorProgram
import InitECandidate.Solver.GasBudget.WarmKeysInitial
import InitECandidate.Solver.GasBudget.WarmKeysLoop
import InitECandidate.Solver.Input.AssignNormal
import InitECandidate.Solver.Input.CounterLoopLocal

namespace InitECandidate.Solver.GasBudget.WarmKeys
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout

/-- Original constructor, counter reset and whole storage-key warming loop
in their actual caller scopes. The constructor establishes the empty table;
only ordinary entry geometry/code/input facts remain premises. -/
theorem constructor_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (cursor start total : Nat) (environment : Environment source)
    (valid : Valid .storage (fresh .storage cursor 16)) (inputValid : MemoryRegion.Valid (inputRegion start total))
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (keys : source.locals.lookup (ofString "al_keys") = some (.val (.word (BitVec.ofNat 64 start))))
    (count : source.locals.lookup (ofString "nkeys") = some (.val (.word (BitVec.ofNat 64 total))))
    (newCode : source.code.lookup (ofString "htab_new") = some (WitnessRadix.TableNew.formals, WitnessRadix.TableNew.body, .one))
    (normal : evaluateHOLFiniteState source constructorSite = (some (.returned value), post)) :
    ∃ paid plan slots nextCursor warmed finish,
      paid ≤ source.clock ∧ warmed.clock = source.clock - paid ∧
      paid + GrowRuntime.growthPotential .storage 16 ≤ 10 + price 0 total + GrowRuntime.growthPotential .storage plan.capacity ∧
      Table warmed plan slots nextCursor cursor ∧ Environment warmed ∧
      Locals warmed (cell plan .header 0) start total total ∧ slots.length ≤ total ∧
      plan.capacity ≤ max 16 (4 * (total + 1)) ∧
      evaluateHOLFiniteState warmed afterLoop = (some (.returned value), finish) ∧ post = restore source "ak" finish ∧
      warmed.code = source.code ∧
      (∀ address : BitVec 64, address.toNat < cursor → warmed.memory address = source.memory address) ∧
      ∀ key : MlS, key ≠ ofString "ak" → key ≠ ofString "i" → warmed.locals.lookup key = source.locals.lookup key := by
  rw [constructor_shape] at normal
  obtain ⟨funded, inner, afterNew, restored⟩ := TableRuntime.call_normal source post .storage cursor 16 "ak" newArguments (.seq resetIndex site)
    valid environment.domain (Or.inr (by decide)) rfl newCode heap environment.allocCode environment.zeroCode value normal
  rw [initial_price] at funded
  let constructed := TableRuntime.callState source "ak" .storage cursor 16
  let ready := bind constructed "i" 0#64
  have resetSafe : Input.LocalPrefix (ofString "nkeys") resetIndex := .assign _ _ (by decide)
  obtain ⟨reset, resetRun, siteRun, _⟩ := resetSafe.normal_continue constructed inner site value afterNew
  have resetEq := Input.assign_none constructed reset "i" (.const 0#64) 0#64 rfl resetRun
  change reset = ready at resetEq
  subst reset
  rw [site_shape] at siteRun
  obtain ⟨warmed, loopRun, restRun, _⟩ := loop_safe.normal_continue ready inner afterLoop value siteRun
  have constructedTable := initial_table source cursor environment valid
  have readyTable : Table ready (fresh .storage cursor 16) [] (freshEnd .storage cursor 16) cursor := constructedTable.of_fields rfl rfl rfl rfl
  have readyEnvironment : Environment ready := environment.of_fields rfl rfl rfl
  obtain ⟨paid, plan, slots, nextCursor, fits, clockEq, bounded, finalTable, finalEnvironment, finalLocals,
    lower, upper, capacityBound, earlierWords⟩ := loop_normal total ready warmed start total 0 cursor (freshEnd .storage cursor 16) (fresh .storage cursor 16) [] inputValid
      (by omega) readyEnvironment readyTable (initial_locals source cursor start total keys count) loopRun
  have readyClock : ready.clock = source.clock - 10 := by
    change source.clock - (TableRuntime.price 16 + 1) = source.clock - 10
    rw [initial_price]
  change paid + GrowRuntime.growthPotential .storage 16 ≤ price 0 total + GrowRuntime.growthPotential .storage plan.capacity at bounded
  change slots.length ≤ 0 + total at upper
  change plan.capacity ≤ max 16 (4 * (0 + total + 1)) at capacityBound
  refine ⟨10 + paid, plan, slots, nextCursor, warmed, inner, by omega, by omega, by omega,
    finalTable, finalEnvironment, finalLocals, by omega, by simpa only [Nat.zero_add] using capacityBound, restRun, restored, ?_, ?_, ?_⟩
  · have fields := Input.evaluation_fields ready warmed loop none loopRun
    exact fields.2.2.2
  · intro address earlier
    exact (earlierWords address earlier).trans (TableRuntime.caller_memory_away source "ak" .storage cursor 16 valid address (Or.inl earlier))
  · intro key notTable notIndex
    have same := Input.counter_loop_local ready warmed condition (ofString "htab_set") [localVar "ak", query, .const 1#64] "i" (.op .add [localVar "i", .const 1#64]) key notIndex loopRun
    calc
      warmed.locals.lookup key = ready.locals.lookup key := same
      _ = constructed.locals.lookup key := by simp [ready, WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, Ne.symm notIndex]
      _ = source.locals.lookup key := by simp [constructed, TableRuntime.callState, WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, Ne.symm notTable]

end InitECandidate.Solver.GasBudget.WarmKeys

#print axioms InitECandidate.Solver.GasBudget.WarmKeys.constructor_normal
