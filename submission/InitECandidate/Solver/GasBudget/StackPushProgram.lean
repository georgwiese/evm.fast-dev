import InitECandidate.Solver.GasBudget.FrameField
import InitECandidate.Solver.Input.NormalDeclarationEntry
import InitECandidate.Solver.Input.ScalarNormal

namespace InitECandidate.Solver.GasBudget.StackPush
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_stack_push with | .function fn => progToHOL fn.body | _ => .skip
def afterSP : ProgHOL 64 := match body with | .dec _ _ _ rest => rest | _ => .skip
def afterCap : ProgHOL 64 := match afterSP with | .dec _ _ _ rest => rest | _ => .skip
def growth : ProgHOL 64 := match afterCap with | .seq first _ => first | _ => .skip
def afterGrowth : ProgHOL 64 := match afterCap with | .seq _ rest => rest | _ => .skip
def growBranch : ProgHOL 64 := match growth with | .ite _ branch _ => branch | _ => .skip
def overflow : ProgHOL 64 := match afterGrowth with | .seq first _ => first | _ => .skip
def writes : ProgHOL 64 := match afterGrowth with | .seq _ rest => rest | _ => .skip
def destination : ExpHOL 64 := .op .add [frameLoad 8#64, .panop .mul [localVar "sp", .const 32#64]]
def nextSP : ExpHOL 64 := .op .add [localVar "sp", .const 1#64]

theorem body_shape : body = .dec (ofString "sp") .one (frameLoad 16#64) afterSP := by
  simp only [body, Guest.guestFn_stack_push, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    Option.map_none, afterSP, frameLoad, frameAddress]

theorem cap_shape : afterSP = .dec (ofString "cap") .one (frameLoad 232#64) afterCap := by
  simp only [body, Guest.guestFn_stack_push, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    Option.map_none, afterSP, afterCap, frameLoad, frameAddress]

theorem growth_shape : afterCap = .seq growth (.seq overflow writes) := by
  simp only [body, Guest.guestFn_stack_push, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    Option.map_none, afterSP, afterCap, growth, afterGrowth, overflow, writes]

theorem choice_shape : growth = .ite (.cmp .notLower (localVar "sp") (localVar "cap")) growBranch .skip := by
  simp only [body, Guest.guestFn_stack_push, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    Option.map_none, afterSP, afterCap, growth, growBranch, localVar]

theorem overflow_shape : overflow = .ite (.cmp .equal (localVar "sp") (.const 1024#64))
    (.raise (ofString "EvmErr") (.const 3#64)) .skip := by
  simp only [body, Guest.guestFn_stack_push, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    Option.map_none, afterSP, afterCap, afterGrowth, overflow, localVar]

theorem writes_shape : writes = .seq (.store destination (localVar "v"))
    (.seq (.store (frameAddress 16#64) nextSP) (.return (.const 0#64))) := by
  simp only [body, Guest.guestFn_stack_push, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil,
    Option.map_none, afterSP, afterCap, afterGrowth, writes, destination, nextSP, localVar, frameLoad, frameAddress]

theorem no_growth (source : PanSemStateFiniteExact 64 Guest.HostMemory) (sp capacity : BitVec 64)
    (spLocal : source.locals.lookup (ofString "sp") = some (.val (.word sp)))
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (room : sp < capacity) : evaluateHOLFiniteState source growth = (none, source) := by
  classical
  have notFull : ¬capacity ≤ sp := by change ¬capacity.toNat ≤ sp.toNat; change sp.toNat < capacity.toNat at room; omega
  have read : eval source (.cmp .notLower (localVar "sp") (localVar "cap")) = some (.val (.word 0#64)) := by
    simp [eval, evalHOLExact, localVar, toExact, spLocal, capLocal, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, notFull]
  simp only [eval] at read
  rw [choice_shape, evaluateHOLFiniteState_ite, read]
  simp [evaluateHOLFiniteState_skip]

theorem no_overflow (source : PanSemStateFiniteExact 64 Guest.HostMemory) (sp capacity : BitVec 64)
    (spLocal : source.locals.lookup (ofString "sp") = some (.val (.word sp)))
    (room : sp < capacity) (bounded : capacity.toNat ≤ 1024) : evaluateHOLFiniteState source overflow = (none, source) := by
  classical
  have different : sp ≠ 1024#64 := by
    intro equal
    have numeric := congrArg BitVec.toNat equal
    change sp.toNat < capacity.toNat at room
    change sp.toNat = 1024 at numeric
    omega
  have read : eval source (.cmp .equal (localVar "sp") (.const 1024#64)) = some (.val (.word 0#64)) := by
    simp [eval, evalHOLExact, localVar, toExact, spLocal, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, different]
  simp only [eval] at read
  rw [overflow_shape, evaluateHOLFiniteState_ite, read]
  simp [evaluateHOLFiniteState_skip]

end InitECandidate.Solver.GasBudget.StackPush

#print axioms InitECandidate.Solver.GasBudget.StackPush.body_shape
#print axioms InitECandidate.Solver.GasBudget.StackPush.cap_shape
#print axioms InitECandidate.Solver.GasBudget.StackPush.growth_shape
#print axioms InitECandidate.Solver.GasBudget.StackPush.choice_shape
#print axioms InitECandidate.Solver.GasBudget.StackPush.overflow_shape
#print axioms InitECandidate.Solver.GasBudget.StackPush.writes_shape
#print axioms InitECandidate.Solver.GasBudget.StackPush.no_growth
#print axioms InitECandidate.Solver.GasBudget.StackPush.no_overflow
