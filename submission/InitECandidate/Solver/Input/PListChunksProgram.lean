import InitECandidate.Solver.Input.ProgressiveCallCost
import InitECandidate.Solver.Input.ProgressiveGlobals
import InitECandidate.Solver.Input.MixLengthCallCost
import InitECandidate.Solver.Input.SszHashWorkspace

namespace InitECandidate.Solver.Input.PListChunks
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_htr_plist_chunks with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "roots",.one),(ofString "n",.one),(ofString "len",.one),(ofString "out",.one)]
def progressiveArguments : List (ExpHOL 64) := [localVar "roots",localVar "n",localVar "out"]
def mixArguments : List (ExpHOL 64) := [localVar "out",localVar "len",localVar "out"]
def afterRoot : ProgHOL 64 := .seq (.call (some (none,none)) (ofString "mix_in_length") mixArguments) (.return (.const 0#64))

theorem body_shape : body=.seq (.call (some (none,none)) (ofString "merkleize_progressive") progressiveArguments) afterRoot := by
  simp only [body,Guest.guestFn_htr_plist_chunks,progToHOL,expToHOL,List.map_cons,List.map_nil,Option.map_none,
    progressiveArguments,mixArguments,afterRoot,localVar]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "htr_plist_chunks")=some (formals,body,.one) := by
  have checked := OriginalCode.indexed code installed 178 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_htr_plist_chunks) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.guestFn_htr_plist_chunks,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem progressive_globals (key : MlS) (code) (installed : OriginalCode.Installed code) (different : key≠ofString "heap_ptr") :
    GlobalEffects.Preserves key code (.call (some (none,none)) (ofString "merkleize_progressive") progressiveArguments) :=
  GlobalEffects.call_body key code (some none) (ofString "merkleize_progressive") progressiveArguments Progressive.formals Progressive.body .one
    (Progressive.original_code code installed) (Progressive.globals key code installed different)

theorem globals (key : MlS) (code) (installed : OriginalCode.Installed code) (different : key≠ofString "heap_ptr") : GlobalEffects.Preserves key code body := by
  rw [body_shape]
  unfold afterRoot
  exact GlobalEffects.sequence key code _ _ (progressive_globals key code installed different)
    (GlobalEffects.sequence key code _ _
      (GlobalEffects.call_body key code (some none) (ofString "mix_in_length") mixArguments MixLength.formals MixLength.body .one
        (MixLength.original_code code installed) (MixLength.globals key code installed)) (GlobalEffects.returned key code _))

end InitECandidate.Solver.Input.PListChunks

#print axioms InitECandidate.Solver.Input.PListChunks.body_shape
#print axioms InitECandidate.Solver.Input.PListChunks.original_code
#print axioms InitECandidate.Solver.Input.PListChunks.progressive_globals
#print axioms InitECandidate.Solver.Input.PListChunks.globals
