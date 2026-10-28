import InitECandidate.Solver.Input.CurrentVerify.GasLimit
import InitECandidate.Solver.Input.UDivMod.CurrentFrame
import InitECandidate.Solver.Input.WordPairConstFrame

namespace InitECandidate.Solver.Input.CurrentVerify.GasLimit
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The current gas-limit check preserves all memory, globals, FFI and
runtime metadata on every outcome. Its constant1024 divisor rules out the
division-by-zero trap from the same actual invocation. -/
theorem readonly (code) (installed : OriginalCode.Installed code) : LocalEffects.Preserves code body := by
  intro source same
  rw [body_shape]
  apply LocalEffects.word_pair_const source (ofString "udiv") (ofString "a") (ofString "b") (ofString "max_delta") UDivMod.Divide.body tail .one .one
    (localVar "parent_gas_limit") 1024#64 (by decide)
    (UDivMod.Divide.original_code source.code (by rw [same]; exact installed))
  · intro entry left codeEq aCell bCell
    exact UDivMod.Divide.nonzero_frame entry left 1024#64 aCell bCell (by decide)
      (UDivMod.original_code entry.code (by rw [codeEq,same]; exact installed))
  · have pure : ∀ program,PureDecision program → LocalEffects.Preserves source.code program := by
      intro program decision
      induction decision with
      | skip=>exact LocalEffects.skip source.code
      | returned expression=>exact LocalEffects.returned source.code expression
      | raised name expression=>exact LocalEffects.raised source.code name expression
      | ite test left right leftIH rightIH=>exact LocalEffects.conditional source.code _ _ _ leftIH rightIH
      | seq front back frontIH backIH=>exact LocalEffects.sequence source.code _ _ frontIH backIH
    exact pure tail tail_decision

end InitECandidate.Solver.Input.CurrentVerify.GasLimit

#print axioms InitECandidate.Solver.Input.CurrentVerify.GasLimit.readonly
