import Guest.Ast
import Flapjack.Pancake.PanLang.Decl
import Mathlib.Tactic

namespace InitECandidate.Solver.MutableTable.OriginalCallSites
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

/-- All syntactic internal call occurrences, including tail calls and
exception handlers. External FFI names are a separate constructor. -/
def mentions (target : MlS) : Prog (BitVec 64) → Bool
  | .call (some (_, some (_, _, handler))) function _ => (target == ofString function) || mentions target handler
  | .call _ function _ => target == ofString function
  | .decCall _ _ function _ rest => (target == ofString function) || mentions target rest
  | .seq first second | .ite _ first second => mentions target first || mentions target second
  | .dec _ _ _ rest | .while _ rest => mentions target rest
  | _ => false
termination_by structural code => code

def declarationMentions (target : MlS) : Decl (BitVec 64) → Bool
  | .function fn => mentions target fn.body
  | _ => false

set_option maxRecDepth 50000 in
set_option maxHeartbeats 3000000 in
/-- The unchanged program contains no internal call to the scratch-copy
routine, including in any exception handler or uncalled function. -/
theorem scratch_copy_no_incoming :
    Guest.guestAst.all (fun declaration => !(declarationMentions (ofString "htab_copy_scratch") declaration)) = true := by
  with_unfolding_all rfl

theorem scratch_copy_no_declaration_call (declaration : Decl (BitVec 64)) (member : declaration ∈ Guest.guestAst) :
    declarationMentions (ofString "htab_copy_scratch") declaration = false := by
  have checked := List.all_eq_true.mp scratch_copy_no_incoming declaration member
  cases value : declarationMentions (ofString "htab_copy_scratch") declaration <;> simp_all

set_option maxRecDepth 50000 in
set_option maxHeartbeats 3000000 in
/-- The persistent clone is called only from original state-root
computation; it is not a per-opcode or recursive EVM-frame operation. -/
theorem persistent_copy_callers :
    Guest.guestAst.filter (declarationMentions (ofString "htab_copy")) = [Guest.guestFn_compute_state_root] := by
  with_unfolding_all rfl

end InitECandidate.Solver.MutableTable.OriginalCallSites

#print axioms InitECandidate.Solver.MutableTable.OriginalCallSites.scratch_copy_no_incoming
#print axioms InitECandidate.Solver.MutableTable.OriginalCallSites.scratch_copy_no_declaration_call
#print axioms InitECandidate.Solver.MutableTable.OriginalCallSites.persistent_copy_callers
