import InitECandidate.Solver.Input.ScratchClear

/- The early-stop results in this module require a cursor at or below
sourceBase. This explicit unmapped-arena premise does not hold at current
main startup; mapped scratch paths need their own execution proofs. -/

namespace InitECandidate.Solver.Input.ScratchConstructors
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def messageBody : ProgHOL 64 := match Guest.Software.guestFn_msg_new_scratch with
  | .function fn => progToHOL fn.body | _ => .skip

theorem message_shape : messageBody =
    .decCall (ofString "m") .one (ofString "scratch_alloc") [.const 176#64]
      (.seq (.call (some (none, none)) (ofString "memzero") [localVar "m", .const 176#64])
        (.return (localVar "m"))) := by
  simp only [messageBody, Guest.Software.guestFn_msg_new_scratch, progToHOL, expToHOL,
    shapeToHOL, localVar, List.map_cons, List.map_nil, Option.map_none]

set_option maxRecDepth 100000 in
theorem message_installed (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "msg_new_scratch") = some ([], messageBody, .one) := by
  have found := OriginalCode.indexed code installed 422
    (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_msg_new_scratch) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, messageBody,
    Guest.Software.guestFn_msg_new_scratch, shapeToHOL, List.map_nil] using found

/-- The actual current scratch message constructor cannot return with ordered
arena cursors below the compiler's ordinary domain. Its own allocator return
and clear are derived, rather than a future mapped buffer being assumed. -/
theorem message_no_return {F : Type} (source post : PanSemStateFiniteExact 64 F)
    (pointer limit : BitVec 64) (value : ValueHOL 64)
    (pointerBound : pointer.toNat ≤ InitE.sourceBase) (ordered : limit ≤ pointer)
    (aligned : limit.toNat % 8 = 0) (domain : source.memaddrs = InitE.ordinaryDomain)
    (installed : OriginalCode.Installed source.code)
    (pointerGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)))
    (limitGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word limit))) :
    evaluateHOLFiniteState source messageBody ≠ (some (.returned value), post) := by
  rw [message_shape]
  exact ScratchClear.allocated_clear_no_return source post pointer limit 176 "m" (.return (localVar "m")) value
    (by decide) (by decide) pointerBound ordered aligned domain installed pointerGlobal limitGlobal

/-- A real caller of this installed constructor cannot return through any
continuation under the same current arena facts. No body return is supplied. -/
theorem message_call_no_return {F : Type} (source post : PanSemStateFiniteExact 64 F)
    (pointer limit : BitVec 64) (name : MlS) (continuation : ProgHOL 64) (value : ValueHOL 64)
    (pointerBound : pointer.toNat ≤ InitE.sourceBase) (ordered : limit ≤ pointer)
    (aligned : limit.toNat % 8 = 0) (domain : source.memaddrs = InitE.ordinaryDomain)
    (installed : OriginalCode.Installed source.code)
    (pointerGlobal : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word pointer)))
    (limitGlobal : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word limit))) :
    evaluateHOLFiniteState source (.decCall name .one (ofString "msg_new_scratch") [] continuation) ≠
      (some (.returned value), post) := by
  intro normal
  have code := message_installed source.code installed
  have raw : lookupCodeHOLExact source.code.lookup (ofString "msg_new_scratch") [] =
      some (messageBody, (fun _ => none), .one) := by
    simp [lookupCodeHOLExact, code]
  obtain ⟨callee, called, _⟩ := WitnessRadix.CodeEnvironment.finite_lookup source.code.lookup
    (ofString "msg_new_scratch") [] messageBody _ .one raw
  have positive := CallNormal.normal_clock source post name .one (ofString "msg_new_scratch") [] continuation value normal
  obtain ⟨target, returned, actual⟩ := CallNormal.callee_return source post name .one (ofString "msg_new_scratch")
    [] [] messageBody continuation callee .one rfl called positive value normal
  exact message_no_return (callEntryStateHOLFinite source callee) target pointer limit returned
    pointerBound ordered aligned domain installed pointerGlobal limitGlobal actual

end InitECandidate.Solver.Input.ScratchConstructors

#print axioms InitECandidate.Solver.Input.ScratchConstructors.message_shape
#print axioms InitECandidate.Solver.Input.ScratchConstructors.message_installed
#print axioms InitECandidate.Solver.Input.ScratchConstructors.message_no_return
#print axioms InitECandidate.Solver.Input.ScratchConstructors.message_call_no_return
