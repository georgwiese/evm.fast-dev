import InitECandidate.Solver.GasBudget.JournalInactive
import InitECandidate.Solver.Input.GlobalFieldRead

namespace InitECandidate.Solver.GasBudget.FrameEpilogue
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

def body : ProgHOL 64 := match Guest.guestFn_frame_epilogue with | .function fn => progToHOL fn.body | _ => .skip
def snapshot : ExpHOL 64 := .load .one (addConst (.var .global (ofString "cur_cont")) 24#64)
def rollback : ProgHOL 64 := .call (some (none, none)) (ofString "state_restore") [snapshot]
def condition : ExpHOL 64 := .cmp .notEqual (frameLoad 160#64) (.const 0#64)
def choice : ProgHOL 64 := .ite condition rollback .skip

theorem body_shape : body = .seq choice (.return (.const 0#64)) := by
  simp only [body, Guest.guestFn_frame_epilogue, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    Option.map_none, choice, condition, frameLoad, frameAddress, rollback, snapshot, addConst]

theorem choice_safe : Input.LocalPrefix (ofString "setup") choice :=
  .ite _ (.call none _ _ (by intro name impossible; cases impossible)) .skip

def nextCount (err : BitVec 64) (count snap : Nat) : Nat := if err = 0#64 then count else min count snap
def removed (err : BitVec 64) (count snap : Nat) : Nat := if err = 0#64 then 0 else count - snap
def price (err : BitVec 64) (population count snap : Nat) : Nat := if err = 0#64 then 0 else Journal.price population (count - snap) + 1

theorem count_balance (err : BitVec 64) (count snap : Nat) : nextCount err count snap + removed err count snap = count := by
  by_cases same : err = 0#64 <;> simp only [nextCount, removed, same, ↓reduceIte] <;> omega

theorem condition_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame err : BitVec 64)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (mapped : source.memaddrs (frame + 160#64)) (stored : source.memory (frame + 160#64) = .word err) :
    eval source condition = some (.val (.word (if err = 0#64 then 0#64 else 1#64))) := by
  have read := frame_read source frame 160#64 err ev mapped stored
  simp only [eval] at read
  simp [eval, condition, evalHOLExact, read, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

end InitECandidate.Solver.GasBudget.FrameEpilogue

#print axioms InitECandidate.Solver.GasBudget.FrameEpilogue.body_shape
#print axioms InitECandidate.Solver.GasBudget.FrameEpilogue.choice_safe
#print axioms InitECandidate.Solver.GasBudget.FrameEpilogue.count_balance
#print axioms InitECandidate.Solver.GasBudget.FrameEpilogue.condition_read
