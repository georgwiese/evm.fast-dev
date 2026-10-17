import Guest.Ast
import InitECandidate.Solver.WitnessRadix.RawProgram

/-! Proposed source program for a replacement target. The challenge still
refers to Guest.guestAst. Equality of observable behavior is NOT claimed here;
it requires the map/memory refinement and all reachable-state premises. -/
namespace InitECandidate.Solver.WitnessRadix.Program
open Flapjack

def replace : Decl (BitVec 64) → Decl (BitVec 64)
  | .function fn =>
      if fn.name = "nodedb_build" then RawProgram.guestFn_nodedb_build
      else if fn.name = "nodedb_lookup" then RawProgram.guestFn_nodedb_lookup
      else .function fn
  | declaration => declaration

/-- Append the helper after the original declarations, preserving existing
function order through the substitution. The parser-only global is excluded. -/
def candidateAst : List (Decl (BitVec 64)) :=
  Guest.guestAst.map replace ++ [RawProgram.guestFn_solver_radix_index]

def nonFunction : Decl (BitVec 64) → Option (Decl (BitVec 64))
  | .function _ => none
  | declaration => some declaration

theorem nonFunction_replace (declaration : Decl (BitVec 64)) :
    nonFunction (replace declaration) = nonFunction declaration := by
  cases declaration with
  | function fn =>
      by_cases build : fn.name = "nodedb_build"
      · simp [replace, build, nonFunction, RawProgram.guestFn_nodedb_build]
      · by_cases lookup : fn.name = "nodedb_lookup"
        · simp [replace, build, lookup, nonFunction, RawProgram.guestFn_nodedb_lookup]
        · simp [replace, build, lookup, nonFunction]
  | decl | exnDecl | name => rfl

theorem nonFunctions_map (declarations : List (Decl (BitVec 64))) :
    (declarations.map replace).filterMap nonFunction = declarations.filterMap nonFunction := by
  induction declarations with
  | nil => rfl
  | cons declaration rest ih =>
      simp only [List.map_cons, List.filterMap_cons, nonFunction_replace, ih]

/-- Scalar globals, exception and struct declarations are literally unchanged. -/
theorem nonFunctions_preserved : candidateAst.filterMap nonFunction =
    Guest.guestAst.filterMap nonFunction := by
  change (Guest.guestAst.map replace ++ [RawProgram.guestFn_solver_radix_index]).filterMap
    nonFunction = _
  rw [List.filterMap_append, nonFunctions_map]
  have helper : nonFunction RawProgram.guestFn_solver_radix_index = none := rfl
  simp only [List.filterMap_cons, helper, List.filterMap_nil, List.append_nil]

def abi : Decl (BitVec 64) → Option (String × List (String × Shape) × Shape)
  | .function fn => some (fn.name, fn.params, fn.returnShape)
  | _ => none

theorem nodedb_build_abi : abi RawProgram.guestFn_nodedb_build = abi Guest.guestFn_nodedb_build := rfl
theorem nodedb_lookup_abi : abi RawProgram.guestFn_nodedb_lookup = abi Guest.guestFn_nodedb_lookup := rfl

end InitECandidate.Solver.WitnessRadix.Program

#print axioms InitECandidate.Solver.WitnessRadix.Program.nonFunctions_preserved
#print axioms InitECandidate.Solver.WitnessRadix.Program.nodedb_build_abi
#print axioms InitECandidate.Solver.WitnessRadix.Program.nodedb_lookup_abi
