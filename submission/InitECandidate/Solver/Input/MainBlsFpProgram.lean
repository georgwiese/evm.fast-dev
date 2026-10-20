import InitECandidate.Solver.Input.MainBlsPairProgram
import InitECandidate.Solver.WitnessRadix.ZeroCost
import InitECandidate.Solver.WitnessRadix.CopyGeneralCall
import InitECandidate.Solver.WitnessRadix.CopyGeneralCode
import InitECandidate.Solver.WitnessRadix.Copy32Alignment

namespace InitECandidate.Solver.Input.Main.BlsFpInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def body : ProgHOL 64 := match Guest.guestFn_fp_accel_init with | .function fn => progToHOL fn.body | _ => .skip
def block : InitializerAllocationAliases.Block :=
  ⟨InitializerAllocations.constant "fp_accel_params" 240,
    [InitializerAliases.direct "fp_accel_params" "fp_accel_a",InitializerAliases.offset "fp_accel_params" "fp_accel_b" 48,
      InitializerAliases.offset "fp_accel_params" "fp_accel_zero" 96,InitializerAliases.offset "fp_accel_params" "fp_accel_d" 192]⟩
def zeroCall : ProgHOL 64 := .call (some (none,none)) (ofString "memzero") [.var .global (ofString "fp_accel_zero"),.const 48#64]
def copyCall : ProgHOL 64 := .call (some (none,none)) (ofString "memcpy")
  [.op .add [.var .global (ofString "fp_accel_params"),.const 144#64],.op .add [.var .global (ofString "bls_c"),.const 48#64],.const 48#64]
def memoryTail : ProgHOL 64 := .seq zeroCall (.seq copyCall (.return (.const 0#64)))
def allocationTail : ProgHOL 64 := InitializerAllocationAliases.withTail [block] memoryTail

theorem body_shape : body = .seq (WordTableInitialization.guard "fp_accel_params") (.seq BlsPairInitialization.constantsCall allocationTail) := by
  simp only [body,WordTableInitialization.guard,BlsPairInitialization.constantsCall,allocationTail,block,memoryTail,zeroCall,copyCall,
    InitializerAllocationAliases.withTail,InitializerAllocations.withTail,InitializerAllocations.call,InitializerAllocations.constant,
    InitializerAliases.withTail,InitializerAliases.direct,InitializerAliases.offset,
    Guest.guestFn_fp_accel_init,progToHOL,expToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

def symbols : List String := ["fp_accel_params","fp_accel_a","fp_accel_b","fp_accel_zero","fp_accel_d"]

open scoped InitE.MetadataComputation InitE.NameComputation in
theorem symbols_checked : (symbols.map ofString).all (fun key => OriginalScalarGlobals.names.contains key) = true := by decide_cbv

theorem symbol_member (name : String) (member : name ∈ symbols) : ofString name ∈ OriginalScalarGlobals.names :=
  List.contains_iff_mem.mp (List.all_eq_true.mp symbols_checked (ofString name) (List.mem_map.mpr ⟨name,member,rfl⟩))

theorem valid : InitializerAllocationAliases.Valid block := by
  refine ⟨InitializerAllocations.valid_constant _ _ (symbol_member _ (by simp [symbols])) (by decide) (by decide),?_,?_⟩
  all_goals intro action member
  all_goals simp only [block,List.mem_cons,List.not_mem_nil,or_false] at member
  all_goals rcases member with rfl | rfl | rfl | rfl
  · exact InitializerAliases.direct_valid _ _ (symbol_member _ (by simp [symbols])) (by decide)
  · exact InitializerAliases.offset_valid _ _ _ (symbol_member _ (by simp [symbols])) (by decide)
  · exact InitializerAliases.offset_valid _ _ _ (symbol_member _ (by simp [symbols])) (by decide)
  · exact InitializerAliases.offset_valid _ _ _ (symbol_member _ (by simp [symbols])) (by decide)
  all_goals decide

theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "fp_accel_init") = some ([],body,.one) := by
  have checked := OriginalCode.indexed code installed 657 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_fp_accel_init) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,Guest.guestFn_fp_accel_init,shapeToHOL,List.map_cons,List.map_nil] using checked

def memoryTemplate (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer constants : BitVec 64) :=
  {source with memory := CopyGeneral.resultMemory (Zero.finalMemory source.memory (pointer + 96#64) 48) source.be (constants + 48#64) (pointer + 144#64) 48}

end InitECandidate.Solver.Input.Main.BlsFpInitialization

#print axioms InitECandidate.Solver.Input.Main.BlsFpInitialization.body_shape
#print axioms InitECandidate.Solver.Input.Main.BlsFpInitialization.symbols_checked
#print axioms InitECandidate.Solver.Input.Main.BlsFpInitialization.symbol_member
#print axioms InitECandidate.Solver.Input.Main.BlsFpInitialization.valid
#print axioms InitECandidate.Solver.Input.Main.BlsFpInitialization.original_code
