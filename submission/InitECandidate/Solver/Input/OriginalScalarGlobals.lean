import InitECandidate.Solver.Input.CallPrefixExecution
import InitECandidate.Solver.Input.ScalarWordShape
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

/-- Every actual evaluator outcome preserves existing scalar global shapes.
The core semantics checks global writes against their previous shapes, so
this needs no guest-body or successful-return hypothesis. -/
theorem Scalars.after {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {program : ProgHOL 64} {result : Option (PanSemResultExact 64)}
    (scalars : Scalars source.globals) (run : evaluateHOLFiniteState source program=(result,post)) : Scalars post.globals := by
  intro key member
  obtain ⟨word,cell⟩:=scalars key member
  obtain ⟨value,present,shape⟩:=evaluateHOLFiniteState_global_shape_invariant source program result post key (.val (.word word)) run cell
  obtain ⟨next,typed⟩:=scalar_word_of_shape value (by simpa only [shapeOfHOLExact] using shape)
  exact ⟨next,by rw [typed] at present; exact present⟩

theorem Scalars.of_frame {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    (scalars : Scalars source.globals) (frame : LocalEffects.erase post=LocalEffects.erase source) : Scalars post.globals := by
  have globals:=congrArg PanSemStateFiniteExact.globals frame
  change post.globals=source.globals at globals
  rw [globals]
  exact scalars

/-- A concrete heap update and an actual frame for every other global
retain all scalar types; allocation room and values are separate facts. -/
theorem Scalars.of_heap_frame {before after : HolFiniteMapExact MlS (ValueHOL 64)}
    (scalars : Scalars before) (heap : BitVec 64)
    (cell : after.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frame : ∀ key,key≠ofString "heap_ptr" → after.lookup key=before.lookup key) : Scalars after := by
  intro key member
  by_cases same : key=ofString "heap_ptr"
  · subst key; exact ⟨heap,cell⟩
  · obtain ⟨word,present⟩:=scalars key member
    exact ⟨word,(frame key same).trans present⟩

/-- Reached lexical prefixes inherit the same scalar globals even when
calls replace locals or final scopes restore them. -/
theorem Scalars.prefix {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {actions : List CallPrefix.Action}
    (scalars : Scalars source.globals) (execution : CallPrefix.Execution source actions post) : Scalars post.globals := by
  have globals:=congrArg PanSemStateFiniteExact.globals execution.skip_erase
  change (evaluateHOLFiniteState source (CallPrefix.program actions .skip)).2.globals=post.globals at globals
  rw [←globals]
  exact scalars.after rfl

set_option maxRecDepth 100000 in
open scoped InitE.MetadataComputation InitE.NameComputation in
theorem evm_names : ofString "evm_empty" ∈ names ∧ ofString "vm_system_address" ∈ names ∧ ofString "beacon_roots_address" ∈ names := by decide_cbv

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

#print axioms InitECandidate.Solver.Input.OriginalScalarGlobals.Scalars.after
#print axioms InitECandidate.Solver.Input.OriginalScalarGlobals.Scalars.of_frame
#print axioms InitECandidate.Solver.Input.OriginalScalarGlobals.Scalars.prefix
#print axioms InitECandidate.Solver.Input.OriginalScalarGlobals.evm_names

#print axioms InitECandidate.Solver.Input.OriginalScalarGlobals.Scalars.of_heap_frame
