import InitECandidate.Solver.GasBudget.RequireNotStaticPrefix
import InitECandidate.Solver.GasBudget.OpcodeChargeSites

namespace InitECandidate.Solver.GasBudget.OpcodeTstore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def body : ProgHOL 64 := match Guest.guestFn_op_tstore with | .function fn => progToHOL fn.body | _ => .skip
def names : List String := ["kv", "v"]
def afterGuard : ProgHOL 64 := match body with | .seq _ rest => rest | _ => .skip
def suffix : ProgHOL 64 := match OpcodeChargeSites.stripPops 2 afterGuard with | .seq _ rest => rest | _ => .skip

theorem body_shape : body = RequireNotStatic.program (OpcodeChargePrefix.program names 100#64 suffix) := by
  simp only [body, Guest.guestFn_op_tstore, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none,
    RequireNotStatic.program, RequireNotStatic.call, OpcodeChargePrefix.program, names, StackPop.pops, StackPop.shape,
    suffix, afterGuard, OpcodeChargeSites.stripPops]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "op_tstore") = some ([], body, .one) := by
  have found : (functionsHOL Input.OriginalCode.program)[488]? =
      some (OriginalCodeEnvironment.originalEntry Guest.guestFn_op_tstore) := by rfl
  have checked := Input.OriginalCode.indexed code installed 488 _ found
  simpa only [OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, Guest.guestFn_op_tstore,
    body, shapeToHOL, List.map_nil] using checked

end InitECandidate.Solver.GasBudget.OpcodeTstore

#print axioms InitECandidate.Solver.GasBudget.OpcodeTstore.body_shape
#print axioms InitECandidate.Solver.GasBudget.OpcodeTstore.original_code
