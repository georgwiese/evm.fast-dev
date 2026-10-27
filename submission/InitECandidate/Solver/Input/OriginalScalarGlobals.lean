import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.Input.DeclarationZeroGlobals

namespace InitECandidate.Solver.Input.OriginalScalarGlobals
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def names := DeclarationCode.globalNames OriginalCode.program

set_option maxRecDepth 100000 in
open scoped InitE.MetadataComputation InitE.NameComputation in
theorem checked : DeclarationCode.zeroGlobalsCheck OriginalCode.program = true := by decide_cbv

set_option maxRecDepth 100000 in
open scoped InitE.MetadataComputation InitE.NameComputation in
theorem count : names.length = 67 := by decide_cbv

def Scalars (globals : HolFiniteMapExact MlS (ValueHOL 64)) : Prop :=
  ∀ key,key ∈ names → ∃ word : BitVec 64,globals.lookup key = some (.val (.word word))

theorem declaration_pass (source target : PanSemStateFiniteExact 64 Guest.HostMemory) [DecidablePred source.memaddrs]
    (run : evaluateDeclsHOLFinite source OriginalCode.program = some target) :
    ∀ key,key ∈ names → target.globals.lookup key = some (.val (.word 0#64)) :=
  fun key member => DeclarationCode.zero_global_lookup source target OriginalCode.program (DeclarationCode.zero_check OriginalCode.program checked) run key member

theorem declaration_scalars (source target : PanSemStateFiniteExact 64 Guest.HostMemory) [DecidablePred source.memaddrs]
    (run : evaluateDeclsHOLFinite source OriginalCode.program = some target) : Scalars target.globals :=
  fun key member => ⟨0#64,declaration_pass source target run key member⟩

theorem Scalars.update {globals : HolFiniteMapExact MlS (ValueHOL 64)} (scalars : Scalars globals) (name : MlS) (word : BitVec 64) :
    Scalars (globals.update (name,.val (.word word))) := by
  intro key member
  by_cases same : key = name
  · subst key
    exact ⟨word,by simp [HolFiniteMapExact.update,FUPDATE]⟩
  · obtain ⟨old,present⟩ := scalars key member
    exact ⟨old,by simp [HolFiniteMapExact.update,FUPDATE,Ne.symm same,present]⟩

set_option maxRecDepth 100000 in
open scoped InitE.MetadataComputation InitE.NameComputation in
theorem sha_names : ofString "sha_st" ∈ names ∧ ofString "sha_pad" ∈ names := by decide_cbv

set_option maxRecDepth 100000 in
open scoped InitE.MetadataComputation InitE.NameComputation in
theorem keccak_names : ofString "keccak_st" ∈ names ∧ ofString "keccak_pad" ∈ names := by decide_cbv

set_option maxRecDepth 100000 in
open scoped InitE.MetadataComputation InitE.NameComputation in
theorem ssz_names : ofString "ssz_len_chunk" ∈ names ∧ ofString "ssz_offs" ∈ names ∧ ofString "zero_hashes" ∈ names := by decide_cbv

set_option maxRecDepth 100000 in
open scoped InitE.MetadataComputation InitE.NameComputation in
theorem mpt_names : ofString "empty_trie_root" ∈ names ∧ ofString "empty_code_hash" ∈ names ∧ ofString "mpt_nib_scratch" ∈ names ∧ ofString "mpt_hash_scratch" ∈ names ∧ ofString "mpt_key_scratch" ∈ names := by decide_cbv

end InitECandidate.Solver.Input.OriginalScalarGlobals

#print axioms InitECandidate.Solver.Input.OriginalScalarGlobals.checked
#print axioms InitECandidate.Solver.Input.OriginalScalarGlobals.count
#print axioms InitECandidate.Solver.Input.OriginalScalarGlobals.declaration_pass
#print axioms InitECandidate.Solver.Input.OriginalScalarGlobals.declaration_scalars
#print axioms InitECandidate.Solver.Input.OriginalScalarGlobals.Scalars.update
#print axioms InitECandidate.Solver.Input.OriginalScalarGlobals.sha_names

#print axioms InitECandidate.Solver.Input.OriginalScalarGlobals.keccak_names

#print axioms InitECandidate.Solver.Input.OriginalScalarGlobals.ssz_names

#print axioms InitECandidate.Solver.Input.OriginalScalarGlobals.mpt_names
