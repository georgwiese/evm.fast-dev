import InitECandidate.Solver.GasBudget.WarmKeysConstructor
import InitECandidate.Solver.MutableTable.TableRuntime.NormalRoom

namespace InitECandidate.Solver.GasBudget.WarmKeys
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout

/-- The reached original storage-table constructor establishes its own
reservation room and empty model before the real warming loop. Neither a
future-layout predicate nor an entry-clock allowance is assumed. -/
theorem constructor_normal_bound (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (cursor start total : Nat) (environment : Environment source)
    (lower : 2701131776 ≤ cursor) (bounded : cursor ≤ 33806089496) (aligned : cursor % 8 = 0)
    (inputValid : MemoryRegion.Valid (inputRegion start total))
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
      ∀ address : BitVec 64, address.toNat < cursor → warmed.memory address = source.memory address := by
  have callRun := normal
  rw [constructor_shape] at callRun
  have valid := TableRuntime.normal_call_layout source post .storage cursor 16 "ak" newArguments (.seq resetIndex site)
    (by decide) lower bounded aligned (by decide) (by decide) (by decide) (by decide) environment.domain rfl newCode heap
    environment.allocCode environment.trapCode environment.zeroCode value callRun
  exact constructor_normal source post value cursor start total environment valid inputValid heap keys count newCode normal

end InitECandidate.Solver.GasBudget.WarmKeys

#print axioms InitECandidate.Solver.GasBudget.WarmKeys.constructor_normal_bound
