import InitECandidate.Solver.Input.InitializerBytes
import InitECandidate.Solver.Input.InitializerAllocations
import InitECandidate.Solver.Input.HeapScopeCost

namespace InitECandidate.Solver.Input.Main.EvmInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def body : ProgHOL 64 := match Guest.guestFn_evm_init with | .function fn => progToHOL fn.body | _ => .skip
def literal : List (BitVec 8) := [84#8,114#8,97#8,110#8,115#8,102#8,101#8,114#8,40#8,97#8,100#8,100#8,114#8,101#8,115#8,115#8,44#8,97#8,100#8,100#8,114#8,101#8,115#8,115#8,44#8,117#8,105#8,110#8,116#8,50#8,53#8,54#8,41#8]
def topicAction := InitializerAllocations.constant "transfer_topic" 32
def systemAction := InitializerAllocations.constant "vm_system_address" 24
def nullAction := InitializerAllocations.constant "null_address" 24
def emptyAction := InitializerAllocations.constant "evm_empty" 8
def keyAction := InitializerAllocations.constant "evm_key_buf" 32
def headerAction := InitializerAllocations.constant "pre_hdr_buf" 96

def finalAllocations := InitializerAllocations.withTail [keyAction,headerAction] (.return (.const 0#64))
def zeroEmpty : ProgHOL 64 := .call (some (none,none)) (ofString "memzero") [.var .global (ofString "evm_empty"),.const 8#64]
def afterEmptyAllocation : ProgHOL 64 := .seq zeroEmpty finalAllocations
def afterNullZero := InitializerAllocations.withTail [emptyAction] afterEmptyAllocation
def zeroNull : ProgHOL 64 := .call (some (none,none)) (ofString "memzero") [.var .global (ofString "null_address"),.const 24#64]
def afterNullAllocation : ProgHOL 64 := .seq zeroNull afterNullZero
def afterSystem := InitializerAllocations.withTail [nullAction] afterNullAllocation

def systemFinalByte : ProgHOL 64 := .storeByte (.op .add [.var .global (ofString "vm_system_address"),.const 19#64]) (.const 254#64)
def afterSystemLoop : ProgHOL 64 := .seq systemFinalByte afterSystem
def systemLoopBody : ProgHOL 64 :=
  .seq (.storeByte (.op .add [.var .global (ofString "vm_system_address"),.var .local (ofString "i")]) (.const 255#64))
    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1#64]))
def systemLoop : ProgHOL 64 := .while (.cmp .less (.var .local (ofString "i")) (.const 20#64)) systemLoopBody
def afterSystemAllocation : ProgHOL 64 := .dec (ofString "i") .one (.const 0#64) (.seq systemLoop afterSystemLoop)
def afterHash := InitializerAllocations.withTail [systemAction] afterSystemAllocation

def topicHash : ProgHOL 64 := .call (some (none,none)) (ofString "keccak256") [.var .local (ofString "s"),.const 33#64,.var .global (ofString "transfer_topic")]
def afterTopicAllocation : ProgHOL 64 := .seq topicHash afterHash
def afterRelease := InitializerAllocations.withTail [topicAction] afterTopicAllocation
def releaseCall : ProgHOL 64 := .call (some (none,none)) (ofString "heap_release") [.var .local (ofString "mark")]
def afterString : ProgHOL 64 := .seq releaseCall afterRelease
def stringStores : ProgHOL 64 := InitializerBytes.stores .local "s" 0 literal afterString
def afterMark : ProgHOL 64 := .decCall (ofString "s") .one (ofString "alloc") [.const 40#64] stringStores

theorem body_shape : body = .decCall (ofString "mark") .one (ofString "heap_mark") [] afterMark := by
  simp only [body,afterMark,stringStores,literal,afterString,releaseCall,afterRelease,afterTopicAllocation,topicHash,afterHash,
    afterSystemAllocation,systemLoop,systemLoopBody,afterSystemLoop,systemFinalByte,afterSystem,afterNullAllocation,zeroNull,afterNullZero,
    afterEmptyAllocation,zeroEmpty,finalAllocations,topicAction,systemAction,nullAction,emptyAction,keyAction,headerAction,
    InitializerBytes.stores,InitializerBytes.address,InitializerAllocations.withTail,InitializerAllocations.call,InitializerAllocations.constant,
    Guest.guestFn_evm_init,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none] <;> rfl

def symbols : List String := ["transfer_topic","vm_system_address","null_address","evm_empty","evm_key_buf","pre_hdr_buf"]

open scoped InitE.MetadataComputation InitE.NameComputation in
theorem symbols_checked : (symbols.map ofString).all (fun key => OriginalScalarGlobals.names.contains key) = true := by decide_cbv

theorem symbol_member (name : String) (member : name ∈ symbols) : ofString name ∈ OriginalScalarGlobals.names :=
  List.contains_iff_mem.mp (List.all_eq_true.mp symbols_checked (ofString name) (List.mem_map.mpr ⟨name,member,rfl⟩))

theorem actions_valid : InitializerAllocations.Valid topicAction ∧ InitializerAllocations.Valid systemAction ∧ InitializerAllocations.Valid nullAction ∧
    InitializerAllocations.Valid emptyAction ∧ InitializerAllocations.Valid keyAction ∧ InitializerAllocations.Valid headerAction := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  all_goals exact InitializerAllocations.valid_constant _ _ (symbol_member _ (by simp [symbols])) (by decide) (by decide)

theorem literal_length : literal.length = 33 := by decide_cbv

theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "evm_init") = some ([],body,.one) := by
  have checked := OriginalCode.indexed code installed 520 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_evm_init) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,Guest.guestFn_evm_init,shapeToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Input.Main.EvmInitialization

#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.body_shape
#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.symbols_checked
#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.symbol_member
#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.actions_valid
#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.literal_length
#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.original_code
