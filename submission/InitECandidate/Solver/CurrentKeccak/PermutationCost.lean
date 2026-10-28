import InitECandidate.Solver.CurrentKeccak.PermutationSyntax
import InitECandidate.Solver.Input.ConstantCounterCost
import InitECandidate.Solver.Input.ClockCostCurrent
import InitECandidate.Solver.Input.ClockCostAssignedBody

namespace InitECandidate.Solver.CurrentKeccak.Permutation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix
open Flapjack.Basis.Pure.MlString Input Input.CounterFlow WitnessRadix.QueryBranch

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem round_quiet (code) : QuietClock.Preserves code roundBody := by
  simp only [roundBody,afterLanes,ClockCost.dropDeclarations,body,Guest.Software.guestFn_keccak_f1600,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  repeat first
    | apply QuietClock.declared
    | apply QuietClock.sequence
    | exact QuietClock.assign code _ _

theorem round_safe : LocalPrefix (ofString "stp") roundBody := by
  simp only [roundBody,afterLanes,ClockCost.dropDeclarations,body,Guest.Software.guestFn_keccak_f1600,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  repeat first
    | apply LocalPrefix.dec _ _ _ (by decide)
    | apply LocalPrefix.seq
    | exact LocalPrefix.assign _ _ (by decide)

theorem round_advance : Advances (ofString "r") 1 roundBody := by
  simp only [roundBody,afterLanes,ClockCost.dropDeclarations,body,Guest.Software.guestFn_keccak_f1600,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  repeat first
    | exact CounterFlow.increment (ofString "r")
    | apply CounterFlow.declared _ _ _ _ _ 1 (by decide)
    | apply CounterFlow.sequence _ _ _ 0 1
    | exact CounterFlow.preserved _ _ (LocalPrefix.assign _ _ (by decide))

theorem stores_quiet (code) : QuietClock.Preserves code storeTail := by
  simp only [storeTail,afterLanes,ClockCost.dropDeclarations,body,Guest.Software.guestFn_keccak_f1600,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  repeat first
    | apply QuietClock.sequence
    | exact QuietClock.store code _ _
    | exact QuietClock.returned code _

/-- The actual software permutation has24 real rounds. Every failed read,
store or timeout is included; the many straight-line operations still need
separate target instruction prices. No accelerated/oracle body is substituted. -/
theorem body_cost (code) : ClockCost.Bound code body 24 := by
  apply ClockCost.declaration_prefix code 25 body 24
  change ClockCost.Bound code afterLanes 24
  rw [after_lanes_shape]
  intro source installed
  apply ClockCost.declared_current source "r" (.const 0#64) 0#64 _ 24 rfl
  let ready:=bind source "r" 0#64
  have rounds:=CounterFlow.constant_loop_cost code (ofString "r") (ofString "stp") roundBody 0 24 (by decide)
    (ClockCost.of_quiet code _ (round_quiet code)) round_advance round_safe ready 0#64 installed (bind_lookup_same _ _ _) (by decide)
  have cost : ready.clock-(evaluateHOLFiniteState ready (.while condition roundBody)).2.clock≤24 := by
    simpa only [condition,localVar,Nat.zero_add,Nat.one_mul,BitVec.toNat_ofNat,Nat.zero_mod,Nat.sub_zero] using rounds
  simpa only [Nat.add_zero] using ClockCost.sequence_current ready (.while condition roundBody) storeTail 24 0 cost
    (ClockCost.of_quiet ready.code _ (stores_quiet ready.code))

theorem call_cost (code) (installed : OriginalCode.Installed code) (arguments : List (ExpHOL 64)) :
    ClockCost.Bound code (.call (some (none,none)) (ofString "keccak_f1600") arguments) 25 :=
  ClockCost.assigned_body code none (ofString "keccak_f1600") arguments formals body .one 24
    (original_code code installed) (body_cost code)

end InitECandidate.Solver.CurrentKeccak.Permutation

#print axioms InitECandidate.Solver.CurrentKeccak.Permutation.round_quiet
#print axioms InitECandidate.Solver.CurrentKeccak.Permutation.round_safe
#print axioms InitECandidate.Solver.CurrentKeccak.Permutation.round_advance
#print axioms InitECandidate.Solver.CurrentKeccak.Permutation.body_cost
#print axioms InitECandidate.Solver.CurrentKeccak.Permutation.call_cost
