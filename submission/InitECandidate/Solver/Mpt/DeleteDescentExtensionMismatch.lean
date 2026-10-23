import InitECandidate.Solver.Mpt.DeleteDescentPure
import InitECandidate.Solver.Mpt.DeleteDescentExtensionProgram
import InitECandidate.Solver.Mpt.DeleteDescentOutputPure

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual shorter-prefix choice retains its genuine registered
node as res, without changing the key, cursors, graph or saved stack. -/
theorem prefix_mismatch_output (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (prefixLength segmentLength : BitVec 64)
    (prefixCell : source.locals.lookup (ofString "pl")=some (.val (.word prefixLength)))
    (lengthCell : source.locals.lookup (ofString "sl")=some (.val (.word segmentLength)))
    (smaller : prefixLength.toNat<segmentLength.toNat) (stopped : model.go=0#64)
    (normal : evaluateHOLFiniteState source prefixChoice=(none,target)) :
    Nonempty (DescentOutput source target key length limit nodeLower pathLower property model) := by
  rw [prefix_dispatch source prefixLength segmentLength prefixCell lengthCell,if_pos smaller] at normal
  have read : eval source (localVar "node")=some (.val (.word model.node)):=by simp [eval,localVar,evalHOLExact,toExact,model.nodeCell]
  have actual:=assign_result_execute source key length limit nodeLower pathLower property model (localVar "node") model.node read
  have endpoint : target=QueryBranch.bind source "res" model.node:=congrArg Prod.snd (normal.symm.trans actual)
  rw [endpoint]
  exact DescentOutput.of_erase source (QueryBranch.bind source "res" model.node) key length limit nodeLower pathLower property model
    (model.bind_result source key length limit nodeLower pathLower property model.node model.nodeMember) rfl rfl rfl rfl stopped rfl

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.prefix_mismatch_output
