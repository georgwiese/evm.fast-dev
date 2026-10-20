import InitECandidate.Solver.Input.MainProgram
import InitECandidate.Solver.Input.InitializerAllocations
import InitECandidate.Solver.WitnessRadix.ByteStore
import InitECandidate.Solver.WitnessRadix.KeccakOriginalEnvironment

namespace InitECandidate.Solver.Input.Main.MptInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def body : ProgHOL 64 := match Guest.guestFn_mpt_init with | .function fn => progToHOL fn.body | _ => .skip
def actions : List InitializerAllocations.Action :=
  [InitializerAllocations.constant "empty_trie_root" 32,InitializerAllocations.constant "empty_code_hash" 32,
   InitializerAllocations.constant "mpt_nib_scratch" 64,InitializerAllocations.constant "mpt_hash_scratch" 40,
   InitializerAllocations.constant "mpt_key_scratch" 16]
def seed : ProgHOL 64 := .storeByte (.var .global (ofString "mpt_hash_scratch")) (.const 128#64)
def rootHash : ProgHOL 64 := .call (some (none,none)) (ofString "keccak256")
  [.var .global (ofString "mpt_hash_scratch"),.const 1#64,.var .global (ofString "empty_trie_root")]
def codeHash : ProgHOL 64 := .call (some (none,none)) (ofString "keccak256")
  [.var .global (ofString "mpt_hash_scratch"),.const 0#64,.var .global (ofString "empty_code_hash")]
def afterAllocation : ProgHOL 64 := .seq seed (.seq rootHash (.seq codeHash (.return (.const 0#64))))
def allocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) := InitializerAllocations.template source cursor actions
def seeded (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :=
  {allocated source cursor with memory := ByteStore.put source.memory source.be (BitVec.ofNat 64 (cursor + 128)) 128#8}

theorem body_shape : body = InitializerAllocations.withTail actions afterAllocation := by
  simp only [body,actions,afterAllocation,seed,rootHash,codeHash,InitializerAllocations.withTail,InitializerAllocations.call,InitializerAllocations.constant,
    Guest.guestFn_mpt_init,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

theorem valid : ∀ action,action ∈ actions → InitializerAllocations.Valid action := by
  intro action member
  simp only [actions,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact InitializerAllocations.valid_constant "empty_trie_root" 32 OriginalScalarGlobals.mpt_names.1 (by decide) (by decide)
  · exact InitializerAllocations.valid_constant "empty_code_hash" 32 OriginalScalarGlobals.mpt_names.2.1 (by decide) (by decide)
  · exact InitializerAllocations.valid_constant "mpt_nib_scratch" 64 OriginalScalarGlobals.mpt_names.2.2.1 (by decide) (by decide)
  · exact InitializerAllocations.valid_constant "mpt_hash_scratch" 40 OriginalScalarGlobals.mpt_names.2.2.2.1 (by decide) (by decide)
  · exact InitializerAllocations.valid_constant "mpt_key_scratch" 16 OriginalScalarGlobals.mpt_names.2.2.2.2 (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "mpt_init") = some ([],body,.one) := by
  have checked := OriginalCode.indexed code installed 223 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_mpt_init) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,Guest.guestFn_mpt_init,shapeToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Input.Main.MptInitialization

#print axioms InitECandidate.Solver.Input.Main.MptInitialization.body_shape
#print axioms InitECandidate.Solver.Input.Main.MptInitialization.valid
#print axioms InitECandidate.Solver.Input.Main.MptInitialization.original_code
