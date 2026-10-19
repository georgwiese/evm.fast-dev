import InitECandidate.Solver.Rlp.Fail
import InitECandidate.Solver.Input.ClockCostCurrentGuard

namespace InitECandidate.Solver.Rlp.Fail
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem guard_price (code) (installed : Input.OriginalCode.Installed code) (test : ExpHOL 64)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailPrice : Nat)
    (tailCost : Input.ClockCost.Bound code continuation tailPrice) :
    Input.ClockCost.Bound code (.seq (.ite test (.call (some (none,none)) (ofString "rlp_fail") arguments) .skip) continuation) (max 1 tailPrice) := by
  intro source codeEq
  have currentInstalled : Input.OriginalCode.Installed source.code := by rw [codeEq]; exact installed
  have front := call_price code installed arguments source codeEq
  have stops : (evaluateHOLFiniteState source (.call (some (none,none)) (ofString "rlp_fail") arguments)).1≠none := by
    intro normal
    exact call_not_normal source _ currentInstalled arguments (Prod.ext normal rfl)
  exact Input.ClockCost.stopping_guard_current source test _ continuation 1 tailPrice stops front (tailCost source codeEq)

/-- A real passed RLP failure guard derives its actual false test and
unchanged state. Invalid tests and actual failing callees cannot pass it. -/
theorem guard_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (test : ExpHOL 64)
    (arguments : List (ExpHOL 64)) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.ite test (.call (some (none,none)) (ofString "rlp_fail") arguments) .skip)=(none,post)) :
    eval source test=some (.val (.word 0#64)) ∧ post=source := by
  classical
  rw [evaluateHOLFiniteState_ite] at normal
  generalize observed : @evalHOLExact 64 Guest.HostMemory _ source.toExact
    (fun address => Classical.propDecidable (source.memaddrs address)) test=read at normal
  cases read with
  | none => cases normal
  | some read =>
    cases read with
    | rStruct fields => cases normal
    | nStruct name fields => cases normal
    | val payload =>
      cases payload with
      | word word =>
        simp only at normal
        by_cases zero : word=0
        · rw [if_pos zero,evaluateHOLFiniteState_skip] at normal
          have wordZero : word=0#64 := zero.trans (by decide)
          exact ⟨by simpa only [eval,wordZero] using observed,(congrArg Prod.snd normal).symm⟩
        · rw [if_neg zero] at normal
          exact (call_not_normal source post installed arguments normal).elim

end InitECandidate.Solver.Rlp.Fail

#print axioms InitECandidate.Solver.Rlp.Fail.guard_price
#print axioms InitECandidate.Solver.Rlp.Fail.guard_normal
