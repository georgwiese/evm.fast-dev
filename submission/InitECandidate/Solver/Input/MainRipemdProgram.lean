import InitECandidate.Solver.Input.MainEntry
import InitECandidate.Solver.Input.WordTableFields

namespace InitECandidate.Solver.Input.Main.RipemdInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def body : ProgHOL 64 := match Guest.guestFn_ripemd160_init with | .function fn => progToHOL fn.body | _ => .skip
def actions : List InitializerAllocations.Action :=
  [InitializerAllocations.constant "rmd_tab" 160,InitializerAllocations.constant "rmd_x" 128,InitializerAllocations.constant "rmd_h" 40,InitializerAllocations.constant "rmd_pad" 128]
def words : List (BitVec 64) := [18364758544493064720#64,10079716825146989895#64,14248650839231647395#64,2764919063900629905#64,16099105460569216260#64,14096706008221550565#64,2419779895833949110#64,15279073663851639135#64,16895767220870911080#64,13344426445381913340#64,9905384649541406699#64,14806603881112131687#64,6324581712619534043#64,14224731476766686923#64,7317203453406000633#64,7849414023404435864#64,13688264971095146457#64,6331469388073975673#64,10330303817214507103#64,13537634492463488088#64]
def stores : ProgHOL 64 := InitializerWords.stores "rmd_tab" 0 words (.return (.const 0#64))
def afterGuard : ProgHOL 64 := InitializerAllocations.withTail actions stores

theorem body_shape : body = .seq (WordTableInitialization.guard "rmd_tab") afterGuard := by
  simp only [body,WordTableInitialization.guard,afterGuard,actions,stores,words,InitializerWords.stores,InitializerAllocations.withTail,
    InitializerAllocations.call,InitializerAllocations.constant,Guest.guestFn_ripemd160_init,progToHOL,expToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

def symbols : List String := ["rmd_tab","rmd_x","rmd_h","rmd_pad"]

open scoped InitE.MetadataComputation InitE.NameComputation in
theorem symbols_checked : (symbols.map ofString).all (fun key => OriginalScalarGlobals.names.contains key) = true := by decide_cbv

theorem symbol_member (name : String) (member : name ∈ symbols) : ofString name ∈ OriginalScalarGlobals.names :=
  List.contains_iff_mem.mp (List.all_eq_true.mp symbols_checked (ofString name) (List.mem_map.mpr ⟨name,member,rfl⟩))

theorem valid : ∀ action ∈ actions,InitializerAllocations.Valid action := by
  intro action member
  simp only [actions,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals exact InitializerAllocations.valid_constant _ _ (symbol_member _ (by simp [symbols])) (by decide) (by decide)

theorem words_length : words.length = 20 := by decide_cbv
theorem action_count : actions.length = 4 := by decide_cbv
theorem total_bytes : InitializerAllocations.totalBytes actions = 456 := by decide_cbv

theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "ripemd160_init") = some ([],body,.one) := by
  have checked := OriginalCode.indexed code installed 562 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_ripemd160_init) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,Guest.guestFn_ripemd160_init,shapeToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Input.Main.RipemdInitialization

#print axioms InitECandidate.Solver.Input.Main.RipemdInitialization.body_shape
#print axioms InitECandidate.Solver.Input.Main.RipemdInitialization.symbols_checked
#print axioms InitECandidate.Solver.Input.Main.RipemdInitialization.symbol_member
#print axioms InitECandidate.Solver.Input.Main.RipemdInitialization.valid
#print axioms InitECandidate.Solver.Input.Main.RipemdInitialization.words_length
#print axioms InitECandidate.Solver.Input.Main.RipemdInitialization.action_count
#print axioms InitECandidate.Solver.Input.Main.RipemdInitialization.total_bytes
#print axioms InitECandidate.Solver.Input.Main.RipemdInitialization.original_code
