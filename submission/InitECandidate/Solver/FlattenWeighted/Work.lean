import InitECandidate.Solver.FlattenWeighted.BasicClock
import InitECandidate.Solver.FlattenWeighted.CallReturn
import InitECandidate.Solver.FlattenWeighted.If
import InitECandidate.Solver.FlattenWeighted.Loop
import InitECandidate.Solver.FlattenWeighted.Jumps

/-! Source-only execution credits. The derivation refers to Stack evaluation,
lookups and branch tests, and contains no target execution or simulation premise. -/
namespace InitECandidate.Solver.FlattenWeighted
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.FlattenBound

/-- Credits for actual source sub-runs. Continuations are required only for the
source result that selects them. One credit covers returning-call setup/join
or a conditional's branch/join; loop back edges and tail calls need no extra
credit because both evaluators consume the same clock there. -/
inductive Work {width : Nat} [NeZero width] {C F : Type} :
    HolProg width → StackSemStateFiniteExact width C F → Nat → Prop where
  | error {prog source} (failed : (StackSemEvaluate.evaluate (prog, source)).1 = some .error) :
      Work prog source 0
  | basic {prog source} (supported : basic prog = true) :
      Work prog source (ticks prog + nodes prog)
  | straight {prog source} (supported : straight prog = true) :
      Work prog source (source.clock - (StackSemEvaluate.evaluate (prog, source)).2.clock + nodes prog)
  | mono {prog source first second} (small : first ≤ second)
      (derivation : Work prog source first) : Work prog source second
  | seq {first second source firstCredit secondCredit}
      (firstWork : Work first source firstCredit)
      (secondWork : ∀ post, StackSemEvaluate.evaluate (first, source) = (none, post) →
        Work second post secondCredit) :
      Work (.seq first second) source (firstCredit + secondCredit)
  | ite {cmp reg ri first second source credits}
      (firstWork : branchChoice cmp reg ri source = some true → Work first source credits)
      (secondWork : branchChoice cmp reg ri source = some false → Work second source credits) :
      Work (.ite cmp reg ri first second) source (credits + 1)
  | loop {body source firstCredit againCredit}
      (bodyWork : Work body source firstCredit)
      (againWork : ∀ post result, StackSemEvaluate.evaluate (body, source) = (result, post) →
        StackSemControl.contLoop result = true → post.clock ≠ 0 →
        Work (.loop body) (StackSemStateOps.decClock post) againCredit) :
      Work (.loop body) source (firstCredit + againCredit)
  | jumpLower {r1 r2 dest source credits}
      (calleeWork : branchChoice .lower r1 (.reg r2) source = some true →
        source.clock ≠ 0 → ∀ prog, sptLookup dest source.code = some prog →
        Work prog (StackSemStateOps.decClock source) credits) :
      Work (.jumpLower r1 r2 dest) source (credits + 1)
  | rawCall {dest source credits}
      (calleeWork : source.clock ≠ 0 → ∀ prelude body,
        sptLookup dest source.code = some (.seq prelude body) →
        Work body (StackSemStateOps.decClock source) credits) :
      Work (.rawCall dest) source credits
  | tailCall {dest handler source credits}
      (calleeWork : source.clock ≠ 0 → ∀ prog,
        StackSemControl.findCode dest source.regs source.code = some prog →
        Work prog (StackSemStateOps.decClock source) credits) :
      Work (.call none dest handler) source credits
  | returningCall {rp link l1 l2 dest handler source calleeCredit nextCredit}
      (calleeWork : source.clock ≠ 0 → ∀ prog,
        StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some prog →
        Work prog (StackSemStateOps.decClock
          (StackSemStateOps.setVar link (.loc l1 l2) source)) calleeCredit)
      (returnWork : ∀ prog post,
        StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some prog →
        StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock
          (StackSemStateOps.setVar link (.loc l1 l2) source)) = (some (.result (.loc l1 l2)), post) →
        Work rp post nextCredit)
      (handlerWork : ∀ prog post hp hs hl, handler = some (hp, hs, hl) →
        StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some prog →
        StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock
          (StackSemStateOps.setVar link (.loc l1 l2) source)) = (some (.exception (.loc hs hl)), post) →
        Work hp post nextCredit) :
      Work (.call (some (rp, link, l1, l2)) dest handler) source (calleeCredit + nextCredit + 1)

/-- A source-work derivation supplies the actual Lab execution witness with
at most four extra clock steps per credit, preserving all original hypotheses
and conclusion fields of the compiler simulation. -/
theorem workPaid {width : Nat} [NeZero width] {C F : Type}
    {prog : HolProg width} {source : StackSemStateFiniteExact width C F} {credits : Nat}
    (derivation : Work prog source credits) : PaidProp credits prog source := by
  induction derivation with
  | error failed =>
    intro tail result post name label continues breaks target hypotheses
    rw [hypotheses.1] at failed
    exact (hypotheses.2.1 failed).elim
  | basic supported => exact basicPaid _ _ supported
  | straight supported =>
    intro tail result post name label continues breaks target hypotheses
    apply paidOfBounded (limit := 0)
    · rw [hypotheses.1]
      simp [budget]
    · exact straightBounded _ _ supported tail result post name label continues breaks target hypotheses
  | mono small _ ih =>
    intro tail result post name label continues breaks target hypotheses
    exact paidMono small (ih tail result post name label continues breaks target hypotheses)
  | seq _ _ firstIH secondIH => exact paidSeq _ _ _ _ _ firstIH secondIH
  | ite _ _ firstIH secondIH => exact paidIfSelected _ _ _ _ _ _ _ firstIH secondIH
  | loop _ _ bodyIH againIH => exact paidLoop _ _ _ _ bodyIH againIH
  | jumpLower _ calleeIH => exact paidJumpLower _ _ _ _ _ calleeIH
  | rawCall _ calleeIH => exact paidRawCall _ _ _ calleeIH
  | tailCall _ calleeIH => exact paidCallTail _ _ _ _ calleeIH
  | returningCall _ _ _ calleeIH returnIH handlerIH =>
    exact paidCallRet _ _ _ _ _ _ _ _ _ calleeIH returnIH handlerIH

end InitECandidate.Solver.FlattenWeighted
#print axioms InitECandidate.Solver.FlattenWeighted.workPaid
