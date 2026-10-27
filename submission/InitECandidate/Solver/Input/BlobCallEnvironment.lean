import InitECandidate.Solver.Input.BlobProgram
import InitECandidate.Solver.WitnessRadix.CodeEnvironment
import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.Input.OriginalEntry

namespace InitECandidate.Solver.Input.Blob
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def returnShape : ShapeHOL := .comb [.one,.one]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "input_blob") = some ([],body,returnShape) := by
  have checked := OriginalCode.indexed code installed 24 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_input_blob) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,returnShape,Guest.Software.guestFn_input_blob,shapeToHOL,List.map_cons,List.map_nil] using checked

theorem environment (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (known : codeFn (ofString "input_blob") = some ([],body,returnShape)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "input_blob") [] = some (body,callee,returnShape) := by
  have raw : lookupCodeHOLExact codeFn (ofString "input_blob") [] = some (body,(fun _ => none),returnShape) := by
    simp [lookupCodeHOLExact,known]
  obtain ⟨callee,called,_⟩ := WitnessRadix.CodeEnvironment.finite_lookup codeFn _ [] body _ returnShape raw
  exact ⟨callee,called⟩

end InitECandidate.Solver.Input.Blob

#print axioms InitECandidate.Solver.Input.Blob.original_code
#print axioms InitECandidate.Solver.Input.Blob.environment
