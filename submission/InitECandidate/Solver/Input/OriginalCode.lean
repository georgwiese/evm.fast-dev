import Guest.SoftwareAst
import InitE.NameComputation
import InitECandidate.Solver.Input.DeclarationCode
import InitECandidate.Solver.Input.EvaluationFields

namespace InitECandidate.Solver.Input.OriginalCode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- The fixed software guest currently named by the challenge. -/
def program : List (DeclHOL 64) := Guest.Software.guestAst.map declToHOL

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
set_option cbv.maxSteps 100000000 in
open scoped InitE.MetadataComputation InitE.NameComputation in
/-- Distinctness of the actual original function names, with no body rewrite. -/
theorem distinct : ((functionsHOL program).map Prod.fst).Nodup := by
  unfold program
  rw [InitE.MetadataComputation.functionNames_toHOL]
  apply InitE.MetadataComputation.nodup_of_sorted_fingerprints
  decide_cbv

/-- Every original function signature is in the real installed code map. -/
def Installed (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) : Prop :=
  ∀ entry ∈ functionsHOL program, code.lookup entry.1 = some entry.2

theorem declaration_pass (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    [DecidablePred source.memaddrs]
    (run : evaluateDeclsHOLFinite source program = some target) : Installed target.code := by
  intro entry member
  exact DeclarationCode.installed source target program run entry.1 entry.2
    (DeclarationCode.lastEntry_of_mem (functionsHOL program) entry.1 entry.2 member distinct)

theorem after_execution (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (body : ProgHOL 64) (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source body = (result, target))
    (installed : Installed source.code) : Installed target.code := by
  rw [(evaluation_fields source target body result run).2.2.2]
  exact installed

theorem indexed (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (installed : Installed code) (index : Nat) (entry : MlS × (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (found : (functionsHOL program)[index]? = some entry) : code.lookup entry.1 = some entry.2 :=
  installed entry (List.mem_of_getElem? found)

end InitECandidate.Solver.Input.OriginalCode

#print axioms InitECandidate.Solver.Input.OriginalCode.distinct
#print axioms InitECandidate.Solver.Input.OriginalCode.declaration_pass
#print axioms InitECandidate.Solver.Input.OriginalCode.after_execution
#print axioms InitECandidate.Solver.Input.OriginalCode.indexed
