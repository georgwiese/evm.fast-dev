import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.Input.DeclarationExceptions

namespace InitECandidate.Solver.Input.OriginalExceptions
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

inductive Kind where
  | TrapErr | RlpErr | SszErr | HdrErr | BlockErr
  | MptErr | TxErr | StateErr | EvmErr | Fail

def Kind.name : Kind → MlS
  | .TrapErr => ofString "TrapErr" | .RlpErr => ofString "RlpErr"
  | .SszErr => ofString "SszErr" | .HdrErr => ofString "HdrErr"
  | .BlockErr => ofString "BlockErr" | .MptErr => ofString "MptErr"
  | .TxErr => ofString "TxErr" | .StateErr => ofString "StateErr"
  | .EvmErr => ofString "EvmErr" | .Fail => ofString "Fail"

set_option maxRecDepth 100000 in
theorem original_shape (kind : Kind) :
    DeclarationCode.lastEntry (DeclarationCode.exceptions OriginalCode.program) kind.name = some .one := by
  have selected : DeclarationCode.lastEntry (DeclarationCode.exceptions OriginalCode.program) kind.name =
      some (shapeToHOL Shape.one) := by cases kind <;> rfl
  simpa only [shapeToHOL] using selected

def Installed (shapes : HolFiniteMapExact MlS ShapeHOL) : Prop :=
  ∀ kind : Kind, shapes.lookup kind.name = some .one

theorem declaration_pass (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    [DecidablePred source.memaddrs]
    (run : evaluateDeclsHOLFinite source OriginalCode.program = some target) : Installed target.eshapes := by
  intro kind
  exact DeclarationCode.exception_installed source target OriginalCode.program run kind.name .one (original_shape kind)

theorem after_execution (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (body : ProgHOL 64) (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source body = (result, target))
    (installed : Installed source.eshapes) : Installed target.eshapes := by
  rw [(evaluation_fields source target body result run).2.2.1]
  exact installed

end InitECandidate.Solver.Input.OriginalExceptions

#print axioms InitECandidate.Solver.Input.OriginalExceptions.original_shape
#print axioms InitECandidate.Solver.Input.OriginalExceptions.declaration_pass
#print axioms InitECandidate.Solver.Input.OriginalExceptions.after_execution
