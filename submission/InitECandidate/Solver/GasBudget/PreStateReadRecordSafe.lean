import InitECandidate.Solver.GasBudget.PreStateReadRecord
import InitECandidate.Solver.MutableTable.SetNoOtherException

namespace InitECandidate.Solver.GasBudget.PreStateReadRecord
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString MutableTable

theorem no_other_exception (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : WarmKeys.Environment source) (forbidden : MlS) (other : ofString "TrapErr" ≠ forbidden) :
    Input.NoNamedException.Safe source.code forbidden body := by
  rw [body_shape]
  exact Input.NoNamedException.sequence source.code forbidden _ _
    (Input.NoNamedException.call_body source.code forbidden (ofString "htab_set") arguments TableCall.formals Set.body .one
      environment.setCode (SetNoOtherException.set_safe source environment forbidden other))
    (Input.NoNamedException.of_all source.code forbidden _ (Input.NoException.returned source.code _))

end InitECandidate.Solver.GasBudget.PreStateReadRecord

#print axioms InitECandidate.Solver.GasBudget.PreStateReadRecord.no_other_exception
