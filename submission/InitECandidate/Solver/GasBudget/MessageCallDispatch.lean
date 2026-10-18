import InitECandidate.Solver.GasBudget.MessageCallProgram
import InitECandidate.Solver.GasBudget.ProcessMessageOpen
import InitECandidate.Solver.Input.AssignedCallNormal

namespace InitECandidate.Solver.GasBudget.MessageCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def recipientCondition : ExpHOL 64 := .cmp .equal (.load .one (addConst (localVar "msg") 24#64)) (.const 0#64)
def invokeMessage : ProgHOL 64 := .call (some (some (.local, ofString "frame"), none)) (ofString "process_message") [localVar "msg"]
def creation : ProgHOL 64 := match afterZero with | .dec _ _ _ (.seq (.ite _ yes _) _) => yes | _ => .skip
def afterDispatch : ProgHOL 64 := match afterZero with | .dec _ _ _ (.seq _ rest) => rest | _ => .skip

theorem dispatch_shape : afterZero = .dec (ofString "frame") .one (.const 0#64)
    (.seq (.ite recipientCondition creation invokeMessage) afterDispatch) := by
  simp only [afterZero, body, creation, afterDispatch, Guest.guestFn_process_message_call, progToHOL,
    expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none, Option.map_some,
    recipientCondition, invokeMessage, localVar, addConst]

theorem recipient_nonzero (source : PanSemStateFiniteExact 64 Guest.HostMemory) (message recipient : BitVec 64)
    (binding : source.locals.lookup (ofString "msg") = some (.val (.word message)))
    (mapped : source.memaddrs (message + 24#64)) (word : source.memory (message + 24#64) = .word recipient)
    (nonzero : recipient ≠ 0#64) : eval source recipientCondition = some (.val (.word 0#64)) := by
  have read := FieldStores.Value.read source "msg" message (.copied 24 recipient) ⟨binding, mapped, word⟩
  change eval source (.load .one (addConst (localVar "msg") 24#64)) = some (.val (.word recipient)) at read
  simp only [eval] at read ⊢
  rw [recipientCondition, evalHOLExact, read]
  simp [evalHOLExact, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, nonzero]

/-- A normal non-creation dispatch actually calls process_message, rather
than assuming a helper result or a chosen trace through its body. -/
theorem dispatch_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (message recipient : BitVec 64)
    (binding : source.locals.lookup (ofString "msg") = some (.val (.word message)))
    (mapped : source.memaddrs (message + 24#64)) (word : source.memory (message + 24#64) = .word recipient)
    (nonzero : recipient ≠ 0#64) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterZero = (some (.returned value), post)) :
    ∃ called finish, evaluateHOLFiniteState (bind source "frame" 0#64) invokeMessage = (none, called) ∧
      evaluateHOLFiniteState called afterDispatch = (some (.returned value), finish) ∧ post = restore source "frame" finish := by
  rw [dispatch_shape] at normal
  obtain ⟨declared, finish, read, _, restRun, restored⟩ := Input.CallNormal.declaration_normal_entry source post "frame" .one (.const 0#64) _ value normal
  have same : declared = .val (.word 0#64) := by simpa [eval, evalHOLExact] using read.symm
  subst declared
  let declared := bind source "frame" 0#64
  have declaredMessage : declared.locals.lookup (ofString "msg") = some (.val (.word message)) :=
    (bind_lookup_other _ "frame" "msg" _ (by decide)).trans binding
  have test := recipient_nonzero declared message recipient declaredMessage mapped word nonzero
  have choose : evaluateHOLFiniteState declared (.ite recipientCondition creation invokeMessage) = evaluateHOLFiniteState declared invokeMessage := by
    simp only [eval] at test
    rw [evaluateHOLFiniteState_ite, test]
    rfl
  change evaluateHOLFiniteState declared (.seq (.ite recipientCondition creation invokeMessage) afterDispatch) = (some (.returned value), finish) at restRun
  rw [evaluateHOLFiniteState_seq_line780, choose] at restRun
  have callSafe : Input.LocalPrefix (ofString "msg") invokeMessage := .call (some (ofString "frame")) _ _ (by intro name same; cases same; decide)
  have info := callSafe.summary declared
  generalize computed : evaluateHOLFiniteState declared invokeMessage = output at restRun info
  obtain ⟨result, called⟩ := output
  cases result with
  | none => exact ⟨called, finish, rfl, restRun, restored⟩
  | some result => exact False.elim (info.2 value (congrArg Prod.fst restRun))

end InitECandidate.Solver.GasBudget.MessageCall

#print axioms InitECandidate.Solver.GasBudget.MessageCall.dispatch_shape
#print axioms InitECandidate.Solver.GasBudget.MessageCall.recipient_nonzero
#print axioms InitECandidate.Solver.GasBudget.MessageCall.dispatch_normal
