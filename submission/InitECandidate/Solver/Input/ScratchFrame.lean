import InitECandidate.Solver.Input.ScratchClear
import InitECandidate.Solver.Arenas.Marks

/- The early-stop results in this module require a cursor at or below
sourceBase. This explicit unmapped-arena premise does not hold at current
main startup; mapped scratch paths need their own execution proofs. -/

namespace InitECandidate.Solver.Input.ScratchFrame
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.Software.guestFn_frame_new with
  | .function fn => progToHOL fn.body | _ => .skip
def afterScratchMark : ProgHOL 64 := match body with | .decCall _ _ _ _ rest => rest | _ => .skip
def afterMarks : ProgHOL 64 := match afterScratchMark with | .decCall _ _ _ _ rest => rest | _ => .skip
def afterClear : ProgHOL 64 := match afterMarks with | .decCall _ _ _ _ (.seq _ rest) => rest | _ => .skip

theorem body_shape : body = .decCall (ofString "stack_mark") .one (ofString "scratch_mark") [] afterScratchMark := by
  simp only [body, afterScratchMark, Guest.Software.guestFn_frame_new, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_none]

theorem after_mark_shape : afterScratchMark =
    .decCall (ofString "mem_mark") .one (ofString "frame_mem_mark") [] afterMarks := by
  simp only [afterScratchMark, afterMarks, body, Guest.Software.guestFn_frame_new, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_none]

theorem after_marks_shape : afterMarks =
    .decCall (ofString "e") .one (ofString "scratch_alloc") [.const 280#64]
      (.seq (.call (some (none, none)) (ofString "memzero") [localVar "e", .const 280#64]) afterClear) := by
  simp only [afterScratchMark, afterMarks, afterClear, body, Guest.Software.guestFn_frame_new, progToHOL, expToHOL,
    shapeToHOL, localVar, List.map_cons, List.map_nil, Option.map_none]

set_option maxRecDepth 100000 in
theorem mark_installed (code) (installed : OriginalCode.Installed code) (direction : Arenas.Direction) :
    code.lookup (ofString (Arenas.markName direction)) = some ([], Arenas.markBody direction, .one) := by
  cases direction with
  | up =>
    have found := OriginalCode.indexed code installed 6
      (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_frame_mem_mark) (by rfl)
    simpa only [GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL,
      Arenas.markName, Arenas.markBody, Guest.Software.guestFn_frame_mem_mark, shapeToHOL, List.map_nil] using found
  | down =>
    have found := OriginalCode.indexed code installed 9
      (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_scratch_mark) (by rfl)
    simpa only [GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL,
      Arenas.markName, Arenas.markBody, Guest.Software.guestFn_scratch_mark, shapeToHOL, List.map_nil] using found

set_option maxRecDepth 100000 in
theorem frame_installed (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "frame_new") = some ([(ofString "msg", .one)], body, .one) := by
  have found := OriginalCode.indexed code installed 423
    (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_frame_new) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, body,
    Guest.Software.guestFn_frame_new, shapeToHOL, paramToHOL, List.map_cons, List.map_nil] using found

/-- The real frame constructor's two cursor snapshots preserve the current
arena facts. Its subsequent actual allocation/clear cannot return; no message
read, fresh mapped frame or later EVM operation is assumed. -/
theorem body_no_return (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer limit : BitVec 64) (value : ValueHOL 64)
    (pointerBound : pointer.toNat ≤ InitE.sourceBase) (ordered : limit ≤ pointer)
    (aligned : limit.toNat % 8 = 0) (domain : source.memaddrs = InitE.ordinaryDomain)
    (installed : OriginalCode.Installed source.code)
    (pointerGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)))
    (limitGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word limit))) :
    evaluateHOLFiniteState source body ≠ (some (.returned value), post) := by
  intro normal
  rw [body_shape] at normal
  have positive := CallNormal.normal_clock source post (ofString "stack_mark") .one (ofString "scratch_mark")
    [] afterScratchMark value normal
  have first := Arenas.mark_call source .down "stack_mark" pointer afterScratchMark
    (mark_installed source.code installed .down) pointerGlobal positive
  simp only [Arenas.markName] at first
  rw [first] at normal
  let marked := bind {source with clock := source.clock - 1} "stack_mark" pointer
  let output := evaluateHOLFiniteState marked afterScratchMark
  have resultEq : output.1 = some (.returned value) := congrArg Prod.fst normal
  have run : evaluateHOLFiniteState marked afterScratchMark = (some (.returned value), output.2) :=
    Prod.ext resultEq rfl
  rw [after_mark_shape] at run
  have positiveAgain := CallNormal.normal_clock marked output.2 (ofString "mem_mark") .one (ofString "frame_mem_mark")
    [] afterMarks value run
  have second := Arenas.mark_call marked .up "mem_mark" limit afterMarks
    (mark_installed marked.code installed .up) limitGlobal positiveAgain
  simp only [Arenas.markName] at second
  rw [second] at run
  let ready := bind {marked with clock := marked.clock - 1} "mem_mark" limit
  let next := evaluateHOLFiniteState ready afterMarks
  have nextEq : next.1 = some (.returned value) := congrArg Prod.fst run
  have actual : evaluateHOLFiniteState ready afterMarks = (some (.returned value), next.2) :=
    Prod.ext nextEq rfl
  rw [after_marks_shape] at actual
  exact ScratchClear.allocated_clear_no_return ready next.2 pointer limit 280 "e" afterClear value
    (by decide) (by decide) pointerBound ordered aligned domain installed pointerGlobal limitGlobal actual

end InitECandidate.Solver.Input.ScratchFrame

#print axioms InitECandidate.Solver.Input.ScratchFrame.body_shape
#print axioms InitECandidate.Solver.Input.ScratchFrame.after_mark_shape
#print axioms InitECandidate.Solver.Input.ScratchFrame.after_marks_shape
#print axioms InitECandidate.Solver.Input.ScratchFrame.mark_installed
#print axioms InitECandidate.Solver.Input.ScratchFrame.frame_installed
#print axioms InitECandidate.Solver.Input.ScratchFrame.body_no_return
