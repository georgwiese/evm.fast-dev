import InitECandidate.Solver.Input.MainBlsConstantsInitialization
import InitECandidate.Solver.Input.InitializerAllocationAliases

namespace InitECandidate.Solver.Input.Main.BlsPairInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

inductive Kind where | fp2 | g1 deriving DecidableEq

def function : Kind → String | .fp2 => "fp2_accel_init" | .g1 => "bls_g1_accel_init"
def paramsName : Kind → String | .fp2 => "fp2_accel_params" | .g1 => "bls_g1_accel_params"
def firstName : Kind → String | .fp2 => "fp2_accel_f1" | .g1 => "bls_g1_accel_p1"
def secondName : Kind → String | .fp2 => "fp2_accel_f2" | .g1 => "bls_g1_accel_p2"
def declaration : Kind → Decl (BitVec 64) | .fp2 => Guest.guestFn_fp2_accel_init | .g1 => Guest.guestFn_bls_g1_accel_init

def block (kind : Kind) : InitializerAllocationAliases.Block :=
  ⟨InitializerAllocations.constant (paramsName kind) 192,
    [InitializerAliases.direct (paramsName kind) (firstName kind),InitializerAliases.offset (paramsName kind) (secondName kind) 96]⟩
def body (kind : Kind) : ProgHOL 64 := match declaration kind with | .function fn => progToHOL fn.body | _ => .skip
def constantsCall : ProgHOL 64 := .call (some (none,none)) (ofString "bls_consts_init") []
def allocationTail (kind : Kind) : ProgHOL 64 := InitializerAllocationAliases.withTail [block kind] (.return (.const 0#64))

theorem body_shape (kind : Kind) : body kind = .seq (WordTableInitialization.guard (paramsName kind)) (.seq constantsCall (allocationTail kind)) := by
  cases kind <;> simp only [body,declaration,WordTableInitialization.guard,paramsName,firstName,secondName,constantsCall,allocationTail,block,
    InitializerAllocationAliases.withTail,InitializerAllocations.withTail,InitializerAllocations.call,InitializerAllocations.constant,
    InitializerAliases.withTail,InitializerAliases.direct,InitializerAliases.offset,
    Guest.guestFn_fp2_accel_init,Guest.guestFn_bls_g1_accel_init,progToHOL,expToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

def symbols : List String := ["fp2_accel_params","fp2_accel_f1","fp2_accel_f2","bls_g1_accel_params","bls_g1_accel_p1","bls_g1_accel_p2"]

open scoped InitE.MetadataComputation InitE.NameComputation in
theorem symbols_checked : (symbols.map ofString).all (fun key => OriginalScalarGlobals.names.contains key) = true := by decide_cbv

theorem symbol_member (name : String) (member : name ∈ symbols) : ofString name ∈ OriginalScalarGlobals.names := by
  exact List.contains_iff_mem.mp (List.all_eq_true.mp symbols_checked (ofString name) (List.mem_map.mpr ⟨name,member,rfl⟩))

theorem valid (kind : Kind) : InitializerAllocationAliases.Valid (block kind) := by
  cases kind
  all_goals refine ⟨InitializerAllocations.valid_constant _ _ (symbol_member _ (by simp [symbols,paramsName])) (by decide) (by decide),?_,?_⟩
  all_goals intro action member
  all_goals simp only [block,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl
  · exact InitializerAliases.direct_valid _ _ (symbol_member _ (by simp [symbols,firstName])) (by decide)
  · exact InitializerAliases.offset_valid _ _ _ (symbol_member _ (by simp [symbols,secondName])) (by decide)
  · decide
  · decide
  · exact InitializerAliases.direct_valid _ _ (symbol_member _ (by simp [symbols,firstName])) (by decide)
  · exact InitializerAliases.offset_valid _ _ _ (symbol_member _ (by simp [symbols,secondName])) (by decide)
  · decide
  · decide

theorem original_code (kind : Kind) (code) (installed : OriginalCode.Installed code) : code.lookup (ofString (function kind)) = some ([],body kind,.one) := by
  cases kind
  · have checked := OriginalCode.indexed code installed 678 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_fp2_accel_init) (by rfl)
    simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,declaration,function,Guest.guestFn_fp2_accel_init,shapeToHOL,List.map_cons,List.map_nil] using checked
  · have checked := OriginalCode.indexed code installed 711 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_bls_g1_accel_init) (by rfl)
    simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,declaration,function,Guest.guestFn_bls_g1_accel_init,shapeToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Input.Main.BlsPairInitialization

#print axioms InitECandidate.Solver.Input.Main.BlsPairInitialization.body_shape
#print axioms InitECandidate.Solver.Input.Main.BlsPairInitialization.symbols_checked
#print axioms InitECandidate.Solver.Input.Main.BlsPairInitialization.symbol_member
#print axioms InitECandidate.Solver.Input.Main.BlsPairInitialization.valid
#print axioms InitECandidate.Solver.Input.Main.BlsPairInitialization.original_code
