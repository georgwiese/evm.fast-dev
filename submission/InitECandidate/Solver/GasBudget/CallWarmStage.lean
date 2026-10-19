import InitECandidate.Solver.GasBudget.CallOpcodeCostProgram
import InitECandidate.Solver.GasBudget.WarmAddressMutationCall
import InitECandidate.Solver.MutableTable.SetNoEvmErr

namespace InitECandidate.Solver.GasBudget.CallOpcode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout

def warmGuard : ProgHOL 64 := .ite (.cmp .equal (localVar "warm") (.const 0#64))
  (.call (some (none, none)) (ofString "warm_address") [localVar "to"]) .skip
def afterWarm : ProgHOL 64 := match afterFee with | .seq _ rest => rest | _ => .skip

set_option maxRecDepth 10000 in
theorem warm_shape : afterFee = .seq warmGuard afterWarm := by
  simp only [afterWarm, warmGuard, afterFee, afterCost, costProgram, afterZero, afterMessage, afterPops,
    body, Guest.guestFn_op_call, OpcodeChargeSites.stripPops, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, localVar]

theorem warm_no_evm_error (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code) :
    Input.NoNamedException.Safe source.code (ofString "EvmErr") warmGuard := by
  exact Input.NoNamedException.conditional source.code _ _ _ _
    (Input.NoNamedException.call_body source.code _ (ofString "warm_address") _ WarmAddressMutation.formals WarmAddressMutation.body .one
      (WarmAddressMutation.original_code source.code installed) (SetNoEvmErr.warm_address_safe source environment))
    (Input.NoNamedException.of_all source.code _ _ (Input.NoException.skip source.code))

theorem warm_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame query warm : BitVec 64)
    (plan : Plan) (slots : List Nat) (cursor floor : Nat) (table : TableState source .account plan slots cursor floor)
    (environment : WarmKeys.Environment source) (installed : Input.OriginalCode.Installed source.code)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (tableMapped : source.memaddrs (frame + 168#64)) (tableCell : source.memory (frame + 168#64) = .word (cell plan .header 0))
    (warmCell : source.locals.lookup (ofString "warm") = some (.val (.word warm)))
    (queryCell : source.locals.lookup (ofString "to") = some (.val (.word query)))
    (queryFits : query.toNat + 20 < 2^64)
    (queryMapped : ∀ offset < 20, source.memaddrs (panByteAlignHOL (width := 64) (WitnessRadix.byteAddress query offset)))
    (run : evaluateHOLFiniteState source warmGuard = (none, post)) :
    ∃ paid nextPlan nextSlots nextCursor, paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
      paid + GrowRuntime.growthPotential .account plan.capacity ≤ 9 * slots.length + 13 + GrowRuntime.growthPotential .account nextPlan.capacity ∧
      TableState post .account nextPlan nextSlots nextCursor floor ∧ WarmKeys.Environment post ∧
      slots.length ≤ nextSlots.length ∧ nextSlots.length ≤ slots.length + 1 ∧
      nextPlan.capacity ≤ max plan.capacity (4 * (nextSlots.length + 1)) ∧
      cell nextPlan .header 0 = cell plan .header 0 ∧ HeapGlobals source post ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite
        {source with globals := post.globals, memory := post.memory, clock := source.clock - paid} ∧
      (∀ address : BitVec 64, address.toNat < floor → post.memory address = source.memory address) ∧ post.locals = source.locals := by
  by_cases zero : warm = 0#64
  · have callRun : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "warm_address") [localVar "to"]) = (none, post) := by
      simpa [warmGuard, evaluateHOLFiniteState_ite, evalHOLExact, toExact, localVar, warmCell,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, zero] using run
    have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [localVar "to"] = some [.val (.word query)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, queryCell]
    exact WarmAddressMutation.call_normal source post frame query plan slots cursor floor table environment installed ev tableMapped tableCell
      queryFits queryMapped [localVar "to"] args callRun
  · have unchanged : post = source := by
      have actual : evaluateHOLFiniteState source warmGuard = (none, source) := by
        simp [warmGuard, evaluateHOLFiniteState_ite, evalHOLExact, toExact, localVar, warmCell,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL, zero, evaluateHOLFiniteState_skip]
      exact congrArg Prod.snd (run.symm.trans actual)
    subst post
    exact ⟨0, plan, slots, cursor, by omega, by simp, by omega, table, environment, by omega, by omega,
      Nat.le_max_left _ _, rfl, HeapGlobals.refl source, by simp, by intro address earlier; rfl, rfl⟩

end InitECandidate.Solver.GasBudget.CallOpcode

#print axioms InitECandidate.Solver.GasBudget.CallOpcode.warm_shape
#print axioms InitECandidate.Solver.GasBudget.CallOpcode.warm_no_evm_error
#print axioms InitECandidate.Solver.GasBudget.CallOpcode.warm_normal
