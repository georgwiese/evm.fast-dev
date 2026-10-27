import Guest.SoftwareAst
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

/-! Declaration-to-code view shared by the current program catalogues. -/
namespace InitECandidate.Solver.GasBudget.OriginalCodeEnvironment
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def originalEntry (declaration : Decl (BitVec 64)) : MlS × (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL) :=
  match declToHOL declaration with
  | .function fn => (fn.name, fn.params, fn.body, fn.returnShape)
  | _ => (ofString "", [], .skip, .one)

end InitECandidate.Solver.GasBudget.OriginalCodeEnvironment
