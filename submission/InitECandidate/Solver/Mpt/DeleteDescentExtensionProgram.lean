import InitECandidate.Solver.Mpt.DeleteBodyProgram

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def prefixArguments : List (ExpHOL 64):=[localVar "seg",localVar "sl",keySuffix,remaining]
def prefixMismatch : ProgHOL 64:=.assign .local (ofString "res") (localVar "node")

theorem prefix_scope_shape : prefixScope=.decCall (ofString "pl") .one (ofString "common_prefix_length") prefixArguments prefixChoice := extension_shapes.2.2.1

theorem prefix_choice_shape : prefixChoice=.ite (.cmp .lower (localVar "pl") (localVar "sl")) prefixMismatch extensionFrameScope := extension_shapes.2.2.2.1

theorem prefix_dispatch (source : PanSemStateFiniteExact 64 Guest.HostMemory) (prefixLength segmentLength : BitVec 64)
    (prefixCell : source.locals.lookup (ofString "pl")=some (.val (.word prefixLength)))
    (lengthCell : source.locals.lookup (ofString "sl")=some (.val (.word segmentLength))) :
    evaluateHOLFiniteState source prefixChoice=
      if prefixLength.toNat<segmentLength.toNat then evaluateHOLFiniteState source prefixMismatch else evaluateHOLFiniteState source extensionFrameScope := by
  rw [prefix_choice_shape,evaluateHOLFiniteState_ite]
  by_cases smaller : prefixLength.toNat<segmentLength.toNat <;>
    simp [evalHOLExact,toExact,localVar,prefixCell,lengthCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,smaller]

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.prefix_scope_shape
#print axioms InitECandidate.Solver.Mpt.DeleteBody.prefix_choice_shape
#print axioms InitECandidate.Solver.Mpt.DeleteBody.prefix_dispatch
