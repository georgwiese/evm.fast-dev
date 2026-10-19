import InitECandidate.Solver.GasBudget.U256FromBeProgram
import InitECandidate.Solver.Input.NoFallthrough
import InitECandidate.Solver.Input.ClockCostScoped
import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment

namespace InitECandidate.Solver.GasBudget.U256FromBe
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

private theorem zero_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (rest : ProgHOL 64) :
    (evaluateHOLFiniteState source (.dec (ofString name) .one (.const 0#64) rest)).2.clock =
      (evaluateHOLFiniteState (bind source name 0#64) rest).2.clock := by
  let output := evaluateHOLFiniteState (bind source name 0#64) rest
  have actual := Input.ScalarScope.declare_execute source output.2 name (.const 0#64) 0#64 rest output.1 rfl rfl
  rw [actual]
  rfl

theorem slow_price (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat) (small : length < 2 ^ 64)
    (limit : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length)))) :
    source.clock - (evaluateHOLFiniteState source slow).2.clock ≤ length := by
  let ready := bind (bind (bind (bind (bind source "l0" 0#64) "l1" 0#64) "l2" 0#64) "l3" 0#64) "i" 0#64
  have counter : ready.locals.lookup (ofString "i") = some (.val (.word 0#64)) := bind_lookup_same _ _ _
  have saved : ready.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length))) := by
    simpa [ready, WitnessRadix.QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString] using limit
  have cost := loop_price ready length small 0#64 counter saved (by simp)
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero] at cost
  simp only [slow, zeros, zero_clock]
  change source.clock - (evaluateHOLFiniteState ready (.seq loop finish)).2.clock ≤ length
  rw [evaluateHOLFiniteState_seq_line780]
  generalize computed : evaluateHOLFiniteState ready loop = output at cost ⊢
  obtain ⟨result, target⟩ := output
  change source.clock - target.clock ≤ length at cost
  cases result with
  | none =>
    change source.clock - (evaluateHOLFiniteState target (.return _)).2.clock ≤ length
    rw [Input.QuietClock.returned target.code _ target rfl]
    exact cost
  | some result => exact cost

set_option maxRecDepth 10000 in
theorem fast_stops : Input.NoFallthrough fast := by
  simp only [fast, body, ArithmeticEffects.Kind.body, ArithmeticEffects.Kind.signature, ArithmeticEffects.Kind.original,
    Guest.guestFn_u256_from_be, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  repeat' first
    | apply Input.NoFallthrough.declared
    | apply Input.NoFallthrough.scoped
    | apply Input.NoFallthrough.sequence
    | exact Input.NoFallthrough.returned _

set_option maxRecDepth 10000 in
theorem fast_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code fast 4 := by
  have entry := OriginalCodeEnvironment.arithmetic code installed .bswap64
  have swap := Input.ClockCost.of_quiet code _ (ArithmeticEffects.quiet_preserves .bswap64 code (by rfl))
  simp only [fast, body, ArithmeticEffects.Kind.body, ArithmeticEffects.Kind.signature, ArithmeticEffects.Kind.original,
    Guest.guestFn_u256_from_be, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  apply Input.ClockCost.declared
  refine Input.ClockCost.scoped_body code _ _ (ofString "bswap64") _ _ _ _ _ 0 3 entry swap ?_
  refine Input.ClockCost.sequence code _ _ 0 3 (Input.ClockCost.assign code _ _) ?_
  refine Input.ClockCost.scoped_body code _ _ (ofString "bswap64") _ _ _ _ _ 0 2 entry swap ?_
  refine Input.ClockCost.sequence code _ _ 0 2 (Input.ClockCost.assign code _ _) ?_
  refine Input.ClockCost.scoped_body code _ _ (ofString "bswap64") _ _ _ _ _ 0 1 entry swap ?_
  refine Input.ClockCost.sequence code _ _ 0 1 (Input.ClockCost.assign code _ _) ?_
  refine Input.ClockCost.scoped_body code _ _ (ofString "bswap64") _ _ _ _ _ 0 0 entry swap ?_
  exact Input.ClockCost.returned code _

set_option maxHeartbeats 1000000 in
theorem body_price (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : Input.OriginalCode.Installed source.code) (length : Nat) (small : length < 2 ^ 64)
    (limit : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length)))) :
    source.clock - (evaluateHOLFiniteState source body).2.clock ≤ max 4 length := by
  classical
  have fastCost := fast_price source.code installed source rfl
  have slowCost := slow_price source length small limit
  have stops := fast_stops source
  rw [body_shape, evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  generalize observed : @evalHOLExact 64 Guest.HostMemory _ source.toExact
    (fun address => Classical.propDecidable (source.memaddrs address)) fastTest = value
  cases value with
  | none => simp
  | some value =>
    cases value with
    | rStruct fields => simp
    | nStruct name fields => simp
    | val payload =>
      cases payload with
      | word word =>
        simp only
        by_cases zero : word = 0
        · rw [if_pos zero, evaluateHOLFiniteState_skip]
          exact slowCost.trans (Nat.le_max_right _ _)
        · rw [if_neg zero]
          generalize computed : evaluateHOLFiniteState source fast = output at fastCost stops ⊢
          obtain ⟨result, target⟩ := output
          cases result with
          | none => exact (stops rfl).elim
          | some result => exact fastCost.trans (Nat.le_max_left _ _)

end InitECandidate.Solver.GasBudget.U256FromBe

#print axioms InitECandidate.Solver.GasBudget.U256FromBe.slow_price
#print axioms InitECandidate.Solver.GasBudget.U256FromBe.fast_stops
#print axioms InitECandidate.Solver.GasBudget.U256FromBe.fast_price
#print axioms InitECandidate.Solver.GasBudget.U256FromBe.body_price
