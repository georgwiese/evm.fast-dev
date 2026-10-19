import InitECandidate.Solver.Mpt.Fail
import InitECandidate.Solver.Input.ClockCostGuardReached

namespace InitECandidate.Solver.Mpt.Fail
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem guard_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (test : ExpHOL 64)
    (arguments : List (ExpHOL 64)) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.ite test (.call (some (none,none)) (ofString "mpt_fail") arguments) .skip)=(none,post)) :
    eval source test=some (.val (.word 0#64)) ∧ post=source := by
  classical
  rw [evaluateHOLFiniteState_ite] at normal
  generalize observed : @evalHOLExact 64 Guest.HostMemory _ source.toExact
    (fun address=>Classical.propDecidable (source.memaddrs address)) test=read at normal
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

theorem lower_guard_bound (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (left right : ExpHOL 64)
    (lhs rhs : BitVec 64) (arguments : List (ExpHOL 64))
    (leftRead : eval source left=some (.val (.word lhs))) (rightRead : eval source right=some (.val (.word rhs)))
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.ite (.cmp .lower left right) (.call (some (none,none)) (ofString "mpt_fail") arguments) .skip)=(none,post)) :
    rhs.toNat≤lhs.toNat := by
  have passed := (guard_normal source post _ arguments installed normal).1
  by_contra excessive
  have lt : lhs.toNat<rhs.toNat := by omega
  simp only [eval] at leftRead rightRead
  have one : eval source (.cmp .lower left right)=some (.val (.word 1#64)) := by
    simp [eval,evalHOLExact,leftRead,rightRead,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,lt]
  have impossible : (1#64 : BitVec 64)=0#64 := by
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using one.symm.trans passed
  exact (by decide : (1#64 : BitVec 64)≠0#64) impossible

theorem guard_reached_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (test : ExpHOL 64)
    (error : BitVec 64) (continuation : ProgHOL 64) (price : Nat)
    (installed : Input.OriginalCode.Installed source.code)
    (tail : evaluateHOLFiniteState source (.ite test (.call (some (none,none)) (ofString "mpt_fail") [.const error]) .skip)=(none,source) →
      source.clock-(evaluateHOLFiniteState source continuation).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source (.seq (.ite test (.call (some (none,none)) (ofString "mpt_fail") [.const error]) .skip) continuation)).2.clock≤max 1 price := by
  apply Input.ClockCost.stopping_guard_reached source test _ continuation 1 price
  · intro normal
    exact call_not_normal source _ installed [.const error] (Prod.ext normal rfl)
  · exact call_price source.code installed [.const error] source rfl
  · exact tail

end InitECandidate.Solver.Mpt.Fail

#print axioms InitECandidate.Solver.Mpt.Fail.guard_normal
#print axioms InitECandidate.Solver.Mpt.Fail.lower_guard_bound
#print axioms InitECandidate.Solver.Mpt.Fail.guard_reached_cost
