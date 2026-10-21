import InitECandidate.Solver.MutableTable.FindAnyStep
import InitECandidate.Solver.MutableTable.HashAny32Cost
import InitECandidate.Solver.MutableTable.FindHeader

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Every original finder outcome changes only locals and source clock,
including failures in the actual hash, comparison, declarations or reads. -/
theorem any_body_readonly (code)
    (hashCode : code.lookup (ofString "htab_hash")=some (Hash.formals,Hash.body,.one))
    (memeqCode : code.lookup (ofString "memeq")=some (Memeq32.formals,Memeq32.body,.one)) :
    Input.LocalEffects.Preserves code body := by
  have tailPure : Input.LocalEffects.Preserves code afterIndex :=
    Input.LocalEffects.sequence code _ _ (Input.LocalEffects.loop code _ _ (any_step_readonly code memeqCode)) (Input.LocalEffects.returned code _)
  have indexPure : Input.LocalEffects.Preserves code afterHash := Input.LocalEffects.declared code _ _ _ _ tailPure
  have callPure : Input.LocalEffects.Preserves code hashCall := Input.LocalEffects.scoped_body code (ofString "h") .one (ofString "htab_hash")
    [localVar "key",localVar "klen"] afterHash Hash.formals Hash.body .one hashCode (HashAny32.readonly code) indexPure
  rw [body_shape]
  apply Input.LocalEffects.declared
  apply Input.LocalEffects.declared
  apply Input.LocalEffects.declared
  apply Input.LocalEffects.declared
  apply Input.LocalEffects.declared
  exact callPure

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.any_body_readonly
