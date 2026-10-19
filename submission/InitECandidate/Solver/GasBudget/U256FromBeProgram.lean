import InitECandidate.Solver.GasBudget.ArithmeticQuietClock
import InitECandidate.Solver.Input.CounterDeclaration
import InitECandidate.Solver.Input.CounterLoopCost

namespace InitECandidate.Solver.GasBudget.U256FromBe
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body := ArithmeticEffects.Kind.u256_from_be.body
def fastTest : ExpHOL 64 := match body with | .seq (.ite test _ _) _ => test | _ => .const 0#64
def fast : ProgHOL 64 := match body with | .seq (.ite _ yes _) _ => yes | _ => .skip
def increment : ProgHOL 64 := .assign .local (ofString "i") (.op .add [localVar "i", .const 1#64])
def choice (clause : Nat × String) : ProgHOL 64 :=
  .ite (.cmp .equal (localVar "w") (.const (BitVec.ofNat 64 clause.1)))
    (.assign .local (ofString clause.2) (.op .or [localVar clause.2, localVar "byte"])) .skip
def branches : List (Nat × String) → ProgHOL 64
  | [] => increment
  | clause :: rest => .seq (choice clause) (branches rest)
def posExpression : ExpHOL 64 := .op .sub [.op .sub [localVar "n", .const 1#64], localVar "i"]
def byteExpression : ExpHOL 64 := .shift .lsl (.loadByte (.op .add [localVar "p", localVar "i"]))
  (.panop .mul [.op .and [localVar "pos", .const 7#64], .const 8#64])
def loopBody : ProgHOL 64 := .dec (ofString "pos") .one posExpression
  (.dec (ofString "byte") .one byteExpression
    (.dec (ofString "w") .one (.shift .lsr (localVar "pos") (.const 3#64))
      (branches [(0, "l0"), (1, "l1"), (2, "l2"), (3, "l3")])))
def loop : ProgHOL 64 := .while (.cmp .lower (localVar "i") (localVar "n")) loopBody
def finish : ProgHOL 64 := .return (.rstruct [localVar "l0", localVar "l1", localVar "l2", localVar "l3"])
def zeros : List String → ProgHOL 64 → ProgHOL 64
  | [], rest => rest
  | name :: names, rest => .dec (ofString name) .one (.const 0#64) (zeros names rest)
def slow : ProgHOL 64 := zeros ["l0", "l1", "l2", "l3", "i"] (.seq loop finish)

set_option maxRecDepth 10000 in
theorem body_shape : body = .seq (.ite fastTest fast .skip) slow := by
  simp only [body, ArithmeticEffects.Kind.body, ArithmeticEffects.Kind.signature, ArithmeticEffects.Kind.original,
    Guest.guestFn_u256_from_be, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none,
    fastTest, fast, slow, zeros, loop, loopBody, branches, choice, increment, posExpression, byteExpression, finish, localVar]

theorem branches_quiet (code) (clauses : List (Nat × String)) : Input.QuietClock.Preserves code (branches clauses) := by
  induction clauses with
  | nil => exact Input.QuietClock.assign code _ _
  | cons clause clauses ih =>
      exact Input.QuietClock.sequence code _ _
        (Input.QuietClock.conditional code _ _ _ (Input.QuietClock.assign code _ _) (Input.QuietClock.skip code)) ih

theorem loop_body_quiet (code) : Input.QuietClock.Preserves code loopBody :=
  Input.QuietClock.declared code _ _ _ _
    (Input.QuietClock.declared code _ _ _ _ (Input.QuietClock.declared code _ _ _ _ (branches_quiet code _)))

theorem branches_safe (key : MlS) (clauses : List (Nat × String))
    (counter : key ≠ ofString "i") (others : ∀ clause ∈ clauses, key ≠ ofString clause.2) : Input.LocalPrefix key (branches clauses) := by
  induction clauses with
  | nil => exact .assign _ _ counter
  | cons clause clauses ih =>
      exact .seq (.ite _ (.assign _ _ (others clause (by simp))) .skip)
        (ih (by intro next member; exact others next (by simp [member])))

theorem branches_advance (clauses : List (Nat × String))
    (others : ∀ clause ∈ clauses, ofString "i" ≠ ofString clause.2) : Input.CounterFlow.Advances (ofString "i") 1 (branches clauses) := by
  induction clauses with
  | nil => exact Input.CounterFlow.increment _
  | cons clause clauses ih =>
    have safe : Input.LocalPrefix (ofString "i") (choice clause) := .ite _ (.assign _ _ (others clause (by simp))) .skip
    exact Input.CounterFlow.sequence _ _ _ 0 1 (Input.CounterFlow.preserved _ _ safe)
      (ih (by intro next member; exact others next (by simp [member])))

theorem loop_advance : Input.CounterFlow.Advances (ofString "i") 1 loopBody := by
  apply Input.CounterFlow.declared _ _ _ _ _ 1 (by decide)
  apply Input.CounterFlow.declared _ _ _ _ _ 1 (by decide)
  apply Input.CounterFlow.declared _ _ _ _ _ 1 (by decide)
  apply branches_advance
  intro clause member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide

theorem loop_limit_safe : Input.LocalPrefix (ofString "n") loopBody := by
  refine .dec _ _ _ (by decide) (.dec _ _ _ (by decide) (.dec _ _ _ (by decide) (branches_safe _ _ (by decide) ?_)))
  intro clause member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> decide

theorem loop_price (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : Nat) (small : length < 2 ^ 64)
    (word : BitVec 64) (counter : source.locals.lookup (ofString "i") = some (.val (.word word)))
    (limit : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length)))) (inside : word.toNat ≤ length) :
    source.clock - (evaluateHOLFiniteState source loop).2.clock ≤ length - word.toNat := by
  simpa only [Nat.zero_add, Nat.one_mul, loop, localVar] using Input.CounterFlow.loop_cost source.code (ofString "i") (ofString "n") loopBody 0 length small
    (Input.ClockCost.of_quiet source.code _ (loop_body_quiet source.code)) loop_advance loop_limit_safe source word rfl counter limit inside

end InitECandidate.Solver.GasBudget.U256FromBe

#print axioms InitECandidate.Solver.GasBudget.U256FromBe.body_shape
#print axioms InitECandidate.Solver.GasBudget.U256FromBe.loop_advance
#print axioms InitECandidate.Solver.GasBudget.U256FromBe.loop_price
