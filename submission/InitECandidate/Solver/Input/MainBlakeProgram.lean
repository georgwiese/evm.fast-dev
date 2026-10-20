import InitECandidate.Solver.Input.MainEntry
import InitECandidate.Solver.Input.InitializerBufferFields
import InitECandidate.Solver.Input.WordTableFields

namespace InitECandidate.Solver.Input.Main.BlakeInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def body : ProgHOL 64 := match Guest.guestFn_blake2_init with | .function fn => progToHOL fn.body | _ => .skip
def sigmaBlock : InitializerAllocationAliases.Block := ⟨InitializerAllocations.constant "b2_sigma" 80,[]⟩
def ivBlock : InitializerAllocationAliases.Block := ⟨InitializerAllocations.constant "b2_iv" 64,[]⟩
def roundBlock : InitializerAllocationAliases.Block := ⟨InitializerAllocations.constant "b2_round" 264,
  [InitializerAliases.offset "b2_round" "b2_v" 8,InitializerAliases.offset "b2_round" "b2_m" 136]⟩
def blocks := [sigmaBlock,ivBlock,roundBlock]
def sigma : List (BitVec 64) := [18364758544493064720#64,3853709921291437230#64,5266788149650328715#64,10305543691612001175#64,15242093322790139145#64,10515720223929181890#64,13270197634454188380#64,11702690517083809725#64,6503616966983130870#64,991893350865389610#64]
def iv : List (BitVec 64) := [7640891576956012808#64,13503953896175478587#64,4354685564936845355#64,11912009170470909681#64,5840696475078001361#64,11170449401992604703#64,2270897969802886507#64,6620516959819538809#64]
def ivStores := InitializerWords.stores "b2_iv" 0 iv (.return (.const 0#64))
def sigmaStores := InitializerWords.stores "b2_sigma" 0 sigma ivStores
def afterGuard := InitializerAllocationAliases.withTail blocks sigmaStores

theorem body_shape : body = .seq (WordTableInitialization.guard "b2_sigma") afterGuard := by
  simp only [body,WordTableInitialization.guard,afterGuard,blocks,sigmaBlock,ivBlock,roundBlock,sigmaStores,ivStores,sigma,iv,
    InitializerWords.stores,InitializerAllocationAliases.withTail,InitializerAllocations.withTail,InitializerAllocations.call,InitializerAllocations.constant,
    InitializerAliases.withTail,InitializerAliases.offset,Guest.guestFn_blake2_init,progToHOL,expToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

def symbols : List String := ["b2_sigma","b2_iv","b2_round","b2_v","b2_m"]

open scoped InitE.MetadataComputation InitE.NameComputation in
theorem symbols_checked : (symbols.map ofString).all (fun key => OriginalScalarGlobals.names.contains key) = true := by decide_cbv

theorem symbol_member (name : String) (member : name ∈ symbols) : ofString name ∈ OriginalScalarGlobals.names :=
  List.contains_iff_mem.mp (List.all_eq_true.mp symbols_checked (ofString name) (List.mem_map.mpr ⟨name,member,rfl⟩))

theorem valid : ∀ block ∈ blocks,InitializerAllocationAliases.Valid block := by
  intro block member
  simp only [blocks,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ⟨InitializerAllocations.valid_constant _ _ (symbol_member _ (by simp [symbols])) (by decide) (by decide),by simp [sigmaBlock],by simp [sigmaBlock]⟩
  · exact ⟨InitializerAllocations.valid_constant _ _ (symbol_member _ (by simp [symbols])) (by decide) (by decide),by simp [ivBlock],by simp [ivBlock]⟩
  · refine ⟨InitializerAllocations.valid_constant _ _ (symbol_member _ (by simp [symbols])) (by decide) (by decide),?_,?_⟩
    all_goals intro action member
    all_goals simp only [roundBlock,List.mem_cons,List.not_mem_nil,or_false] at member
    all_goals rcases member with rfl | rfl
    · exact InitializerAliases.offset_valid _ _ _ (symbol_member _ (by simp [symbols])) (by decide)
    · exact InitializerAliases.offset_valid _ _ _ (symbol_member _ (by simp [symbols])) (by decide)
    · decide
    · decide

theorem sigma_length : sigma.length = 10 := by decide_cbv
theorem iv_length : iv.length = 8 := by decide_cbv
theorem block_count : blocks.length = 3 := by decide_cbv
theorem total_bytes : InitializerAllocationAliases.totalBytes blocks = 408 := by decide_cbv

theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "blake2_init") = some ([],body,.one) := by
  have checked := OriginalCode.indexed code installed 568 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_blake2_init) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,Guest.guestFn_blake2_init,shapeToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Input.Main.BlakeInitialization

#print axioms InitECandidate.Solver.Input.Main.BlakeInitialization.body_shape
#print axioms InitECandidate.Solver.Input.Main.BlakeInitialization.symbols_checked
#print axioms InitECandidate.Solver.Input.Main.BlakeInitialization.symbol_member
#print axioms InitECandidate.Solver.Input.Main.BlakeInitialization.valid
#print axioms InitECandidate.Solver.Input.Main.BlakeInitialization.sigma_length
#print axioms InitECandidate.Solver.Input.Main.BlakeInitialization.iv_length
#print axioms InitECandidate.Solver.Input.Main.BlakeInitialization.block_count
#print axioms InitECandidate.Solver.Input.Main.BlakeInitialization.total_bytes
#print axioms InitECandidate.Solver.Input.Main.BlakeInitialization.original_code
