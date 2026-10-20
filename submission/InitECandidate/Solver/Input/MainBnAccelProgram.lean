import InitECandidate.Solver.Input.MainEntry
import InitECandidate.Solver.Input.InitializerAliases
import InitECandidate.Solver.Input.InitializerQuads

namespace InitECandidate.Solver.Input.Main.BnAccelInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def body : ProgHOL 64 := match Guest.guestFn_bn254_accel_init with | .function fn => progToHOL fn.body | _ => .skip
def paramsAction := InitializerAllocations.constant "bn_accel_params" 160
def fp2Action := InitializerAllocations.constant "bn_accel_fp2_params" 128
def g1Action := InitializerAllocations.constant "bn_accel_g1_params" 128
def paramsAliases : List InitializerAliases.Action :=
  [InitializerAliases.direct "bn_accel_params" "bn_accel_a",InitializerAliases.offset "bn_accel_params" "bn_accel_b" 32,
   InitializerAliases.offset "bn_accel_params" "bn_accel_zero" 64,InitializerAliases.offset "bn_accel_params" "bn_accel_m" 96,
   InitializerAliases.offset "bn_accel_params" "bn_accel_d" 128]
def fp2Aliases : List InitializerAliases.Action :=
  [InitializerAliases.direct "bn_accel_fp2_params" "bn_accel_fp2_f1",InitializerAliases.offset "bn_accel_fp2_params" "bn_accel_fp2_f2" 64]
def g1Aliases : List InitializerAliases.Action :=
  [InitializerAliases.direct "bn_accel_g1_params" "bn_accel_g1_p1",InitializerAliases.offset "bn_accel_g1_params" "bn_accel_g1_p2" 64]
def zeros : InitializerQuads.Words := fun _ => 0#64
def modulus : InitializerQuads.Words := fun index => match index.val with
  | 0 => 4332616871279656263#64
  | 1 => 10917124144477883021#64
  | 2 => 13281191951274694749#64
  | _ => 3486998266802970665#64

def afterG1Allocation := InitializerAliases.withTail g1Aliases (.return (.const 0#64))
def afterFp2Aliases := InitializerAllocations.withTail [g1Action] afterG1Allocation
def afterFp2Allocation := InitializerAliases.withTail fp2Aliases afterFp2Aliases
def afterModulus := InitializerAllocations.withTail [fp2Action] afterFp2Allocation
def afterZero := InitializerQuads.stores "bn_accel_m" 0 [modulus] afterModulus
def afterParamsAliases := InitializerQuads.stores "bn_accel_zero" 0 [zeros] afterZero
def afterParamsAllocation := InitializerAliases.withTail paramsAliases afterParamsAliases
def afterGuard := InitializerAllocations.withTail [paramsAction] afterParamsAllocation
def guard : ProgHOL 64 := .ite (.cmp .notEqual (.var .global (ofString "bn_accel_params")) (.const 0#64)) (.return (.const 0#64)) .skip

def params (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :=
  InitializerAliases.template (InitializerAllocations.template source cursor [paramsAction]) (BitVec.ofNat 64 cursor) paramsAliases
def seeded (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :=
  InitializerQuads.written (InitializerQuads.written (params source cursor) (BitVec.ofNat 64 (cursor + 64)) 0 [zeros]) (BitVec.ofNat 64 (cursor + 96)) 0 [modulus]
def fp2 (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :=
  InitializerAliases.template (InitializerAllocations.template (seeded source cursor) (cursor + 160) [fp2Action]) (BitVec.ofNat 64 (cursor + 160)) fp2Aliases
def template (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :=
  InitializerAliases.template (InitializerAllocations.template (fp2 source cursor) (cursor + 288) [g1Action]) (BitVec.ofNat 64 (cursor + 288)) g1Aliases

theorem body_shape : body = .seq guard afterGuard := by
  simp only [body,guard,afterGuard,afterParamsAllocation,afterParamsAliases,afterZero,afterModulus,afterFp2Allocation,afterFp2Aliases,afterG1Allocation,
    paramsAction,fp2Action,g1Action,paramsAliases,fp2Aliases,g1Aliases,zeros,modulus,
    InitializerAllocations.withTail,InitializerAllocations.call,InitializerAllocations.constant,InitializerAliases.withTail,InitializerAliases.direct,InitializerAliases.offset,
    InitializerQuads.stores,InitializerQuads.address,InitializerQuads.expression,Guest.guestFn_bn254_accel_init,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  rfl

def symbols : List String := ["bn_accel_params","bn_accel_a","bn_accel_b","bn_accel_zero","bn_accel_m","bn_accel_d",
  "bn_accel_fp2_params","bn_accel_fp2_f1","bn_accel_fp2_f2","bn_accel_g1_params","bn_accel_g1_p1","bn_accel_g1_p2"]

open scoped InitE.MetadataComputation InitE.NameComputation in
theorem symbols_checked : (symbols.map ofString).all (fun key => OriginalScalarGlobals.names.contains key) = true := by decide_cbv

theorem symbol_member (name : String) (member : name ∈ symbols) : ofString name ∈ OriginalScalarGlobals.names := by
  have present := List.all_eq_true.mp symbols_checked (ofString name) (List.mem_map.mpr ⟨name,member,rfl⟩)
  exact List.contains_iff_mem.mp present

theorem params_valid : InitializerAllocations.Valid paramsAction :=
  InitializerAllocations.valid_constant _ _ (symbol_member _ (by simp [symbols])) (by decide) (by decide)
theorem fp2_valid : InitializerAllocations.Valid fp2Action :=
  InitializerAllocations.valid_constant _ _ (symbol_member _ (by simp [symbols])) (by decide) (by decide)
theorem g1_valid : InitializerAllocations.Valid g1Action :=
  InitializerAllocations.valid_constant _ _ (symbol_member _ (by simp [symbols])) (by decide) (by decide)

theorem params_aliases_valid : ∀ action,action ∈ paramsAliases → InitializerAliases.Valid "bn_accel_params" action := by
  intro action member
  simp only [paramsAliases,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact InitializerAliases.direct_valid _ _ (symbol_member _ (by simp [symbols])) (by decide)
  all_goals exact InitializerAliases.offset_valid _ _ _ (symbol_member _ (by simp [symbols])) (by decide)

theorem fp2_aliases_valid : ∀ action,action ∈ fp2Aliases → InitializerAliases.Valid "bn_accel_fp2_params" action := by
  intro action member
  simp only [fp2Aliases,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact InitializerAliases.direct_valid _ _ (symbol_member _ (by simp [symbols])) (by decide)
  · exact InitializerAliases.offset_valid _ _ _ (symbol_member _ (by simp [symbols])) (by decide)

theorem g1_aliases_valid : ∀ action,action ∈ g1Aliases → InitializerAliases.Valid "bn_accel_g1_params" action := by
  intro action member
  simp only [g1Aliases,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact InitializerAliases.direct_valid _ _ (symbol_member _ (by simp [symbols])) (by decide)
  · exact InitializerAliases.offset_valid _ _ _ (symbol_member _ (by simp [symbols])) (by decide)

theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "bn254_accel_init") = some ([],body,.one) := by
  have checked := OriginalCode.indexed code installed 592 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_bn254_accel_init) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,Guest.guestFn_bn254_accel_init,shapeToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Input.Main.BnAccelInitialization

#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.body_shape
#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.symbols_checked
#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.symbol_member
#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.params_valid
#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.fp2_valid
#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.g1_valid
#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.params_aliases_valid
#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.fp2_aliases_valid
#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.g1_aliases_valid
#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.original_code
