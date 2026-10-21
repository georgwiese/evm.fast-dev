import InitECandidate.Solver.MutableTable.HashByteRuntime.Program
import InitECandidate.Solver.Input.NoFallthrough
import InitECandidate.Solver.Input.QuietClock

set_option maxRecDepth 100000

namespace InitECandidate.Solver.MutableTable.HashAny32
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def side (aligned : Bool) : ProgHOL 64 := match HashByteRuntime.front with | .ite _ yes no=>if aligned then yes else no | _=>.skip
def twenty (aligned : Bool) : ProgHOL 64 := match side aligned with | .seq (.ite _ yes _) _=>yes | _=>.skip
def afterTwenty (aligned : Bool) : ProgHOL 64 := match side aligned with | .seq _ rest=>rest | _=>.skip
def thirtyTwo (aligned : Bool) : ProgHOL 64 := match afterTwenty aligned with | .seq (.ite _ yes _) _=>yes | _=>.skip
def afterThirtyTwo (aligned : Bool) : ProgHOL 64 := match afterTwenty aligned with | .seq _ rest=>rest | _=>.skip
def sizeTest (length : BitVec 64) : ExpHOL 64 := .cmp .equal (localVar "key_len") (.const length)
def alignmentTest : ExpHOL 64 := .cmp .equal (.op .and [localVar "p",.const 7#64]) (.const 0#64)

theorem front_shape : HashByteRuntime.front=.ite alignmentTest (side true) (side false) := by
  simp only [HashByteRuntime.front,Hash.afterLocals,Hash.body,Guest.guestFn_htab_hash,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    side,alignmentTest,localVar]
  rfl

theorem side_shape (aligned : Bool) : side aligned=
    .seq (.ite (sizeTest 20#64) (twenty aligned) .skip)
      (.seq (.ite (sizeTest 32#64) (thirtyTwo aligned) .skip) (afterThirtyTwo aligned)) := by
  cases aligned <;>
    simp only [side,twenty,afterTwenty,thirtyTwo,afterThirtyTwo,HashByteRuntime.front,Hash.afterLocals,Hash.body,Guest.guestFn_htab_hash,
      progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,sizeTest,localVar] <;> rfl

/-- Both literal32-byte branches are unrolled local assignments followed
by return. They spend no body clock and cannot enter the fallback loops. -/
theorem core_summary (aligned : Bool) (code) : Input.QuietClock.Preserves code (thirtyTwo aligned) ∧
    Input.NoFallthrough (thirtyTwo aligned) := by
  cases aligned <;> constructor
  all_goals
    simp only [thirtyTwo,afterTwenty,side,HashByteRuntime.front,Hash.afterLocals,Hash.body,Guest.guestFn_htab_hash,
      progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  all_goals
    repeat first
      | apply Input.QuietClock.sequence
      | exact Input.QuietClock.assign code _ _
      | exact Input.QuietClock.returned code _
      | apply Input.NoFallthrough.sequence
      | exact Input.NoFallthrough.returned _

end InitECandidate.Solver.MutableTable.HashAny32

#print axioms InitECandidate.Solver.MutableTable.HashAny32.front_shape
#print axioms InitECandidate.Solver.MutableTable.HashAny32.side_shape
#print axioms InitECandidate.Solver.MutableTable.HashAny32.core_summary
