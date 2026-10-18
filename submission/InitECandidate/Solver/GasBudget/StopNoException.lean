import InitECandidate.Solver.GasBudget.DispatchStop
import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment
import InitECandidate.Solver.Input.NoExceptionCall

namespace InitECandidate.Solver.GasBudget
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem PcAdd.no_exception (code) : Input.NoException.Safe code PcAdd.body := by
  rw [PcAdd.body_shape]
  exact Input.NoException.sequence code _ _ (Input.NoException.store code _ _) (Input.NoException.returned code _)

theorem Stop.no_exception (code)
    (pcCode : code.lookup (ofString "pc_add") = some (PcAdd.formals, PcAdd.body, .one)) :
    Input.NoException.Safe code Stop.body := by
  rw [Stop.body_shape]
  apply Input.NoException.sequence
  · exact Input.NoException.store code _ _
  · apply Input.NoException.sequence
    · exact Input.NoException.call_body code (ofString "pc_add") [.const 1#64] PcAdd.formals PcAdd.body .one pcCode (PcAdd.no_exception code)
    · exact Input.NoException.returned code _

theorem OpcodeDispatch.stop_no_exception (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : Input.OriginalCode.Installed source.code)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word 0#64))) (identifier : MlS) (payload : ValueHOL 64) :
    (evaluateHOLFiniteState source OpcodeDispatch.body).1 ≠ some (.exception identifier payload) := by
  rw [OpcodeDispatch.body_choice source 0#64 opLocal, OpcodeDispatch.selection_stop, OpcodeDispatch.Action.program]
  have helper := Input.NoException.call_body source.code (ofString "op_stop") [] [] Stop.body .one
    (OriginalCodeEnvironment.op_stop source.code installed) (Stop.no_exception source.code (OriginalCodeEnvironment.pc_add source.code installed))
  exact Input.NoException.sequence source.code _ _ helper (Input.NoException.returned source.code _) source rfl identifier payload

end InitECandidate.Solver.GasBudget

#print axioms InitECandidate.Solver.GasBudget.PcAdd.no_exception
#print axioms InitECandidate.Solver.GasBudget.Stop.no_exception
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.stop_no_exception
